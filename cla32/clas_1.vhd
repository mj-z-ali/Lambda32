library IEEE;
use IEEE.std_logic_1164.all;

entity clas_1 is 
	
    port (
    		a_1, a_0, b_1, b_0, ci : in bit;
            s : out bit);
            
end entity clas_1;
            
architecture clas_1_arc of clas_1 is

begin

	s <=  (a_1 and a_0 and b_1 and b_0) or
          (a_1 and a_0 and b_1 and ci) or
          (a_1 and b_1 and b_0 and ci) or
          (a_1 and not a_0 and not b_1 and not b_0) or
          (a_1 and not a_0 and not b_1 and not ci) or
          (a_1 and not b_1 and not b_0 and not ci) or
          (not a_1 and a_0 and not b_1 and b_0) or
          (not a_1 and a_0 and not b_1 and ci) or
          (not a_1 and b_1 and not b_0 and not ci) or
          (not a_1 and not a_0 and b_1 and not b_0) or
          (not a_1 and not a_0 and b_1 and not ci) or
          (not a_1 and not b_1 and b_0 and ci);

end architecture clas_1_arc;
            