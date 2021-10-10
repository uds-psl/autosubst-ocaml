-- Signature for System F

-- the types
chan : Type
proc : Type

-- the constructors for proc
Nil : proc 
Bang : proc -> proc 
Res : (bind chan in proc) -> proc
Par : proc -> proc -> proc 
In : chan -> (bind chan in proc) -> proc
Out : chan -> chan -> proc -> proc


