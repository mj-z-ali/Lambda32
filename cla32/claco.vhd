library IEEE;
use IEEE.std_logic_1164.all;


entity claco is
	
    port(
    	
        a_1, a_0, b_1, b_0, ci : in bit;
        co : out bit);
        
end entity claco;

architecture claco_arc of claco is


begin

  co <= (a_1 and a_0 and b_0) or
        (a_1 and a_0 and ci) or
        (a_1 and b_0 and ci) or 
        (a_1 and b_1) or
        (a_0 and b_1 and ci) or 
        (a_0 and b_1 and b_0) or
        (b_1 and b_0 and ci); 

end architecture claco_arc;

