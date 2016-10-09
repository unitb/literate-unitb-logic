
import Logic.UnitTest
import System.Exit
import Test.UnitTest

import Logic.Test as Logic
import Z3.Test as Z3

main :: IO ()
main = do
    r <- run_test_cases $ 
        test_cases "literate-unitb-logic test suite" 
            [ Logic.test_case 
            , Z3.test_case ]
    if r
        then exitSuccess
        else exitFailure
