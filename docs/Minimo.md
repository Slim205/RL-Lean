# Minimo : 


Conjecturing : 
generating with controlled diffucukty ? how ? 
big mass of non valid statment.

use constaint decoding to have valid conjectures

the set of conjecturers is a C

using teh llm to generate part by part of the conjecture using constraint decoding.

general format of the context : 
e::= type |prop |x|(ee) |(lambda x: e,e) |[(x: e) →e]. 


ok so if I want to summerize what they are doing in minima : 
they defined a type theory and used it to guid constraint decoding for the llm. for each incomplete sequence, we can mask what are the next possible tokens. this will enable us to have a valid conjectures.

so they start by determining the context, so at least u have less research space for the conjecture and then generate the rest of the conjecture using rules 
