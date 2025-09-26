import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.CommonDefinitions.STLCDefinitions

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for type, term

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`
-- for both `type` & `term`

/-- info: instEnumSizedType -/
#guard_msgs in
#synth EnumSized type

/-- info: instEnumSizedTerm -/
#guard_msgs in
#synth EnumSized term

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum type

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum term

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(error) in
#derive_enum type

#guard_msgs(error) in
#derive_enum term

end CommandElaboratorTest
