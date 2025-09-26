import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveRegExpGenerator

set_option guard_msgs.diff true

deriving instance Enum for RegExp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedRegExp -/
#guard_msgs in
#synth EnumSized RegExp

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum RegExp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(error) in
#derive_enum RegExp

end CommandElaboratorTest
