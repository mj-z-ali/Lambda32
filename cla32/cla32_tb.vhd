-- Code your testbench here
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.NUMERIC_std.ALL;

entity cla32_tb is

end entity cla32_tb;

architecture cla32_tb_arc of cla32_tb is

    signal a_int : integer := 10;
    signal b_int : integer := 15;
    
    signal a: bit_vector(31 downto 0); 
    signal b: bit_vector(31 downto 0);
    signal cin: bit := '0';
    signal s_old : bit_vector(31 downto 0);
    signal co_old : bit;
    signal p_state, n_state : bit_vector(15 downto 0) := (others => '0');
    signal s_new : bit_vector(31 downto 0);
    signal co_new : bit;
    
    signal clock : std_logic := '0';


begin

	a <= to_bitvector(std_logic_vector(to_unsigned(a_int, a'length)));
   	b <= to_bitvector(std_logic_vector(to_unsigned(b_int, b'length)));

	cla32_ins : entity work.cla32(cla32_arc) 
    port map (
    		a => a,
            b => b,
            cin => cin,
            s_old => s_old,
            co_old => co_old,
            p_state => p_state,
            s => s_new,
            cout => co_new);
         
            

	
    clk : process 
    
    begin
    
    	clock <= '0';
        
        wait for 5 ns;
        
        clock <= '1';
        
        wait for 5 ns;
        
     
    end process clk;
    
    
    
    cla32_fsm : process (clock)
    
    begin
    
    	if rising_edge(clock) then
        
        	n_state(0) <= not(
            				p_state(0) or
                            p_state(1) or
                            p_state(2) or
                            p_state(3) or
                            p_state(4) or
                            p_state(5) or
                            p_state(6) or
                            p_state(7) or
                            p_state(8) or
                            p_state(9) or
                            p_state(10) or
                            p_state(11) or
                            p_state(12) or
                            p_state(13) or
                            p_state(14) or
                            p_state(15));                         
            n_state(1) <= p_state(0);
            n_state(2) <= p_state(1);
            n_state(3) <= p_state(2);
            n_state(4) <= p_state(3);
            n_state(5) <= p_state(4);
            n_state(6) <= p_state(5);
            n_state(7) <= p_state(6);
            n_state(8) <= p_state(7);
            n_state(9) <= p_state(8);
            n_state(10) <= p_state(9);
            n_state(11) <= p_state(10);
            n_state(12) <= p_state(11);
            n_state(13) <= p_state(12);
            n_state(14) <= p_state(13);
            n_state(15) <= p_state(14);
            
            p_state <= n_state;
            
            
        end if;
    
    end process cla32_fsm;
    
    state : process (p_state)
    
    begin
    
    	s_old <= s_new;
            
        co_old <= co_new;
    
    end process state;
    

end architecture cla32_tb_arc;