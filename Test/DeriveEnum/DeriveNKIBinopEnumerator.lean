import Plausible.Arbitrary
import Plausible.Chamelean.DeriveEnum
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrary.DeriveNKIBinopGenerator

set_option guard_msgs.diff true

deriving instance Enum for BinOp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedBinOp -/
#guard_msgs in
#synth EnumSized BinOp

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum BinOp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(error) in
#derive_enum BinOp

end CommandElaboratorTest
