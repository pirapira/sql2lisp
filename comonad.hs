-- Future Comonad Implimentation

import Control.Concurrent

type Key = String
type Val = Int

data Thread = T0 | T1
data Agent = T Thread | K Key    
data Data = D Val | S Agent Data

data KeyCommand = WR Key Val

type ThreadCommand = IO ()

