import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveNKIValueGenerator

deriving instance Enum for NKIValue

set_option guard_msgs.diff true

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedNKIValue -/
#guard_msgs in
#synth EnumSized NKIValue

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum NKIValue

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(error) in
#derive_enum NKIValue

end CommandElaboratorTest
