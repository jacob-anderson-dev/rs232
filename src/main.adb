with Ada.Text_IO;
with Ada.Integer_Text_IO;
with Ada.Numerics.Float_Random; use Ada.Numerics.Float_Random;
with Ada.Command_Line;

procedure Main is

    -- Main data types we will be using.
    subtype Byte            is Integer range 0 .. 255;
    subtype Word            is Integer range 0 .. 65_535;
    subtype Address         is Integer range 0 .. 4_095;
    subtype Register_Index  is Integer range 0 .. 15;
    subtype Bit             is Integer range 0 .. 1;

    -- Helper types for bitwise operations.
    type Mod_Byte           is mod 256;
    type Mod_Word           is mod 65_536;
    type Mod_Address        is mod 4_095;
    type Mod_Register_Index is mod 16;
    type Mod_Bit            is mod 2;

    -- Memory, Registers, and Stack Definitions
    type Memory_Array is array (Address) of Byte;
    type Register_Array is array (Register_Index) of Byte;
    type Stack_Array is array (Register_Index) of Word;

    -- Display
    type Display_Array is array (0 .. 32, 0 .. 64) of Bit;

    -- Font
    type Font_Array is array (0 .. 79) of Byte;

    -- CHIP-8 Components
    Memory    : Memory_Array;
    Registers : Register_Array := (others => 0);
    Stack     : Stack_Array;

    -- Display
    Display : Display_Array := (others => (others => 0));

    -- Keys
    Keys : Byte := 0;

    -- Font
    -- Character is always 5 rows tall, and 8 bits wide.
    -- Drawn with DXYN instruction.
    Font : Font_Array :=
       (16#F0#, 16#90#, 16#90#, 16#90#, 16#F0#, 16#20#, 16#60#, 16#20#, 16#20#,
        16#70#, 16#F0#, 16#10#, 16#F0#, 16#80#, 16#F0#, 16#F0#, 16#10#, 16#F0#,
        16#10#, 16#F0#, 16#90#, 16#90#, 16#F0#, 16#10#, 16#10#, 16#F0#, 16#80#,
        16#F0#, 16#10#, 16#F0#, 16#F0#, 16#80#, 16#F0#, 16#90#, 16#F0#, 16#F0#,
        16#10#, 16#20#, 16#40#, 16#40#, 16#F0#, 16#90#, 16#F0#, 16#90#, 16#F0#,
        16#F0#, 16#90#, 16#F0#, 16#10#, 16#F0#, 16#F0#, 16#90#, 16#F0#, 16#90#,
        16#90#, 16#E0#, 16#90#, 16#E0#, 16#90#, 16#E0#, 16#F0#, 16#80#, 16#80#,
        16#80#, 16#F0#, 16#E0#, 16#90#, 16#90#, 16#90#, 16#E0#, 16#F0#, 16#80#,
        16#F0#, 16#80#, 16#F0#, 16#F0#, 16#80#, 16#F0#, 16#80#, 16#80#);

    -- Special Registers
    Index_Register  : Word           := 0;
    Program_Counter : Word           := 512; -- Programs start at 0x200
    Stack_Pointer   : Register_Index := 0;

    -- Timers
    Delay_Timer : Byte := 0;
    Sound_Timer : Byte := 0;

    -- Opcode Implementations
    procedure Execute_Opcode (Op : Word) is

        NNN          : Word           :=
           Op mod 2**12;                                    -- Last 12 bits.
        NN           : Byte           :=
           Byte (Op mod 2**8);                              -- Last byte.
        N            : Byte           :=
           Byte (Op mod 2**4);                              -- 4th nibble.
        X            : Register_Index :=
           Register_Index (Op / 2**8 mod 2**4);   -- 2nd nibble.
        Y            : Register_Index :=
           Register_Index (Op / 2**4 mod 2**4);   -- 3rd nibble.
        First_Nibble : Byte           :=
           Byte (Op / 2**12);                     -- 1st nibble.

        -- Binary to decimal help.
        BCD_X : Register_Index := X;

        -- Generator for random number in RND instruction.
        Gen : Generator;

    begin
        case First_Nibble is

-------------------------------------------------------------------------------------
--  00E0: CLS
--  00EE: RET
-------------------------------------------------------------------------------------

            when 0 =>
                if N = 16#E# then
                    -- RET
                    Program_Counter := Stack (Stack_Pointer);
                    Stack_Pointer   := Stack_Pointer - 1;
                else
                    -- CLS
                    Display := (others => (others => 0));
                end if;

-------------------------------------------------------------------------------------
--  1nnn: JP addr
-------------------------------------------------------------------------------------

            when 1 =>
                Program_Counter := NNN;

-------------------------------------------------------------------------------------
--  2nnn - CALL addr
-------------------------------------------------------------------------------------

            when 2 =>
                Stack (Stack_Pointer) := Program_Counter;
                Stack_Pointer         := Stack_Pointer + 1;
                Program_Counter       := NNN;

-------------------------------------------------------------------------------------
--  3xkk - SE Vx, byte
-------------------------------------------------------------------------------------

            when 3 =>
                if Registers (X) = NN then
                    Program_Counter := Program_Counter + 2;
                end if;

-------------------------------------------------------------------------------------
--  4xkk - SNE Vx, byte
-------------------------------------------------------------------------------------

            when 4 =>
                if Registers (X) /= NN then
                    Program_Counter := Program_Counter + 2;
                end if;

-------------------------------------------------------------------------------------
--  5xy0 - SE Vx, Vy
-------------------------------------------------------------------------------------

            when 5 =>
                if Registers (X) = Registers (Y) then
                    Program_Counter := Program_Counter + 2;
                end if;

-------------------------------------------------------------------------------------
--  6xnn - LD Vx, byte
-------------------------------------------------------------------------------------

            when 6 =>
                Registers (X) := NN;

-------------------------------------------------------------------------------------
--  7xnn - ADD Vx, byte
-------------------------------------------------------------------------------------

            when 7 =>
                Registers (X) := Registers (X) + NN;

-------------------------------------------------------------------------------------
--  8xy0 - LD Vx, Vy
--  8xy1 - OR Vx, Vy
--  8xy2 - AND Vx, Vy
--  8xy3 - XOR Vx, Vy
--  8xy4 - ADD Vx, Vy
--  8xy5 - SUB Vx, Vy
--  8xy6 - SHR Vx
--  8xy7 - SUBN Vx, Vy
--  8xyE - SHL Vx, Vy
-------------------------------------------------------------------------------------

            when 8 =>
                case N is
                    -- LD Vx, Vy
                    when 0 =>
                        Registers (X) := Registers (Y);

                        -- OR Vx, Vy
                    when 1 =>
                        Registers (X) :=
                           Byte
                              (Mod_Byte (Registers (X)) or
                               Mod_Byte (Registers (Y)));

                        -- AND Vx, Vy
                    when 2 =>
                        Registers (X) :=
                           Byte
                              (Mod_Byte (Registers (X)) and
                               Mod_Byte (Registers (Y)));

                        -- XOR Vx, Vy
                    when 3 =>
                        Registers (X) :=
                           Byte
                              (Mod_Byte (Registers (X)) xor
                               Mod_Byte (Registers (Y)));

                        -- ADD Vx, Vy
                    when 4 =>
                        if ((Registers (X) + Registers (Y)) > 255) then
                            Registers (16#F#) := 1;
                        else
                            Registers (16#F#) := 0;
                        end if;
                        Registers (X) := Registers (X) + Registers (Y);

                        -- SUB Vx, Vy
                    when 5 =>
                        if Registers (X) > Registers (Y) then
                            Registers (16#F#) := 1;
                        else
                            Registers (16#F#) := 0;
                        end if;
                        Registers (X) := Registers (X) - Registers (Y);

                        -- SHR Vx
                    when 6 =>
                        if (Mod_Byte (Registers (X)) and Mod_Byte (1)) = 1 then
                            Registers (16#F#) := 1;
                        else
                            Registers (16#F#) := 0;
                        end if;
                        Registers (X) := Registers (X) / 2;

                        -- SUBN Vx, Vy
                    when 7 =>
                        if Registers (Y) > Registers (X) then
                            Registers (16#F#) := 1;
                        else
                            Registers (16#F#) := 0;
                        end if;
                        Registers (X) := Registers (Y) - Registers (X);

                        -- SHL Vx, Vy
                    when 16#E# =>
                        if (Mod_Byte (Registers (X)) and Mod_Byte (128)) = 128
                        then
                            Registers (16#F#) := 1;
                        else
                            Registers (16#F#) := 0;
                        end if;
                        Registers (X) := Registers (X) * 2;

                        -- Any other.
                    when others =>
                        null;

                end case;

-------------------------------------------------------------------------------------
--  9xy0 - SNE Vx, Vy
-------------------------------------------------------------------------------------

            when 9 =>
                if Registers (X) /= Registers (Y) then
                    Program_Counter := Program_Counter + 2;
                end if;

-------------------------------------------------------------------------------------
--  Annn - LD I, addr
-------------------------------------------------------------------------------------

            when 16#A# =>
                Index_Register := NNN;

-------------------------------------------------------------------------------------
--  Bnnn - JP V0, addr
-------------------------------------------------------------------------------------

            when 16#B# =>
                Program_Counter := NNN + Word (Registers (0));

-------------------------------------------------------------------------------------
--  Cxnn - RND Vx, byte
-------------------------------------------------------------------------------------

            when 16#C# =>
                Registers (X) :=
                   Byte (Mod_Byte (Random (Gen)) and Mod_Byte (NN));

-------------------------------------------------------------------------------------
--  Dxyn - DRW Vx, Vy, nibble
-------------------------------------------------------------------------------------

            when 16#D# =>
                for I in 0 .. (N - 1) loop
                    for J in 0 .. 7 loop
                        declare
                            Current_Memory_Bit : Boolean :=
                               ((Mod_Byte (Memory (Index_Register + I)) and
                                 2**J) /=
                                0);
                        begin
                            if Current_Memory_Bit then
                                if (Display
                                       (Registers (Y) + I, Registers (X) + J) =
                                    1)
                                then
                                    Registers (16#F#) := 1;
                                else
                                    Registers (16#F#) := 0;
                                end if;
                                Display
                                   (Registers (Y) + I, Registers (X) + J) :=
                                   Bit
                                      (not Mod_Bit
                                          (Display
                                              (Registers (Y) + I,
                                               Registers (X) + J)));
                            end if;
                        end;
                    end loop;
                end loop;

-------------------------------------------------------------------------------------
--  Ex9E - SKP Vx
--  ExA1 - SKNP Vx
-------------------------------------------------------------------------------------

            when 16#E# =>
                if N = 16#E# then
                    -- SKP Vx
                    if Keys = Registers (X) then
                        Program_Counter := Program_Counter + 2;
                    end if;
                else
                    -- SKNP Vx
                    if not (Keys = Registers (X)) then
                        Program_Counter := Program_Counter + 2;
                    end if;
                end if;

-------------------------------------------------------------------------------------
--  Fx07 - LD Vx, DT
--  Fx0A - LD Vx, K
--  Fx15 - LD DT, Vx
--  Fx18 - LD ST, Vx
--  Fx1E - ADD I, Vx
--  Fx29 - LD F, Vx
--  Fx33 - LD B, Vx
--  Fx55 - LD [I], Vx
--  Fx65 - LD Vx, [I]
-------------------------------------------------------------------------------------

            when 16#F# =>
                case NN is
                    -- LD Vx, DT
                    when 16#07# =>
                        Registers (X) := Delay_Timer;

                        -- LD Vx, K
                    when 16#0A# =>
                        if Keys /= 0 then
                            Registers (X) := Keys;
                        else
                            Program_Counter := Program_Counter + 2;
                        end if;

                        -- LD DT, Vx
                    when 16#15# =>
                        Delay_Timer := Registers (X);

                        -- LD ST, Vx
                    when 16#18# =>
                        Sound_Timer := Registers (X);

                        -- ADD I, Vx
                    when 16#1E# =>
                        Index_Register := Index_Register + Registers (X);

                        -- LD F, Vx
                    when 16#29# =>
                        Index_Register :=
                           Word (16#050#) + Word (5 * Registers (X));

                        -- LD B, Vx
                    when 16#33# =>
                        Memory (Index_Register + 0) := BCD_X mod 10;
                        BCD_X                       := BCD_X / 10;
                        Memory (Index_Register + 1) := BCD_X mod 10;
                        BCD_X                       := BCD_X / 10;
                        Memory (Index_Register + 2) := BCD_X mod 10;

                        -- LD [I], Vx
                    when 16#55# =>
                        for I in 0 .. (Registers (X) - 1) loop
                            Memory (Index_Register + I) := Registers (I);
                        end loop;

                        -- LD Vx, [I]
                    when 16#65# =>
                        for I in 0 .. (Registers (X) - 1) loop
                            Registers (I) := Memory (Index_Register + I);
                        end loop;

                        -- Any others.
                    when others =>
                        null;
                end case;

-------------------------------------------------------------------------------------
-- Any other instructions and no-op.
-------------------------------------------------------------------------------------

            when others =>
                null;

-------------------------------------------------------------------------------------

        end case;
    end Execute_Opcode;

    -- Main Emulation Loop.
    procedure Emulation_Loop is
        Current_Opcode : Word;
    begin
        loop
            -- Fetch Opcode.
            Current_Opcode :=
                Word (Memory (Program_Counter)) * 2**8 +
                Word (Memory (Program_Counter + 1));

            -- Increment Program Counter.
            Program_Counter := Program_Counter + 2;

            -- Execute Opcode.
            Execute_Opcode (Current_Opcode);

            -- Delay Timer.
            if Delay_Timer > 0 then
                Delay_Timer := Delay_Timer - 1;
            end if;

            -- Sound Timer.
            if Sound_Timer > 0 then
                Sound_Timer := Sound_Timer - 1;
            end if;

            -- Emulate the Display.
            for Row in Display'First (1) .. Display'Last (1) loop
                for Col in Display'First (2) .. Display'Last (2) loop
                    -- Do something to display the whole thing.
                    null;
                end loop;
            end loop;

            -- Emulate the Sound.

            -- Simple stopper for use while testing.
            exit when Program_Counter = 1_024;
        end loop;
    end Emulation_Loop;

begin
    -- Load Font into Memory.
    for I in Font'First .. Font'Last loop
        Memory (16#050# + I) := Font (I);
    end loop;

    -- Load ROM into Memory.
    -- Get file name for ROM from launch args.
    -- Start by opening a file.
    -- Now read it into into Memory @ 16#200#.
    -- Close the file.

    -- Start the emulation loop
    Emulation_Loop;

end Main;
