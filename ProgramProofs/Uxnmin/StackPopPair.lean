import ProgramProofs.Uxnmin.PopPair

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

inductive StackPermutation where
  | nip | swp | rot | ovr
  deriving DecidableEq

def StackPermutation.entry : StackPermutation → Word
  | .nip => 0x3c0 | .swp => 0x3ca | .rot => 0x3d7 | .ovr => 0x3f5

theorem StackPermutation.call (operator : StackPermutation) (memory : Word → Byte) (offset : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory) (position : offset = 0 ∨ offset = 3) :
    Uxn.step (machine memory (operator.entry + offset) working returning) = .done (.next
      (machine memory 0x2ad working (Stack.pushWord returning (operator.entry + offset + 3)))) := by
  apply jsi_call
  · cases operator <;> rcases position with rfl | rfl <;>
      exact code _ (by decide) (by decide) (by simp [StackPermutation.entry, MutableCode])
  · have high : memory (operator.entry + offset + 1) =
        ((0x2ad - (operator.entry + offset + 3)) >>> 8).setWidth 8 := by
      cases operator <;> rcases position with rfl | rfl <;>
        exact code _ (by decide) (by decide) (by simp [StackPermutation.entry, MutableCode])
    have low : memory (operator.entry + offset + 2) =
        (0x2ad - (operator.entry + offset + 3)).setWidth 8 := by
      cases operator <;> rcases position with rfl | rfl <;>
        exact code _ (by decide) (by decide) (by simp [StackPermutation.entry, MutableCode])
    rw [high, low, append_split]

end ProgramProofs.Uxnmin
