import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.CommonDefinitions.BinaryTree

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for BinaryTree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedBinaryTree -/
#guard_msgs in
#synth EnumSized BinaryTree

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum BinaryTree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(error) in
#derive_enum BinaryTree

end CommandElaboratorTest
