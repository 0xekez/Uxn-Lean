import ProgramProofs.Uxnmin.OperandRepresentation

namespace ProgramProofs.Uxnmin
open Uxn

/-- A native write to any byte in either guest stack preserves the exterior. -/
theorem StackScratch.data_separate {address : Word} (outside : ¬ StackScratch address)
    (ret : Bool) (index : Byte) : address ≠ stackBase ret + index.setWidth 16 := by
  intro equal
  apply outside
  right
  rw [equal]
  cases ret <;> dsimp [stackBase] <;> constructor <;> bv_omega

theorem StackScratch.pointer_separate {address : Word} (outside : ¬ StackScratch address)
    (ret : Bool) : address ≠ stackBase ret + 0x100#16 := by
  intro equal
  apply outside
  right
  rw [equal]
  cases ret <;> decide

theorem StackScratch.cursor_separate {address : Word} (outside : ¬ StackScratch address)
    (ret keep : Bool) :
    address ≠ stackBase ret + (0x100#16 + (if keep then 1#8 else 0#8).setWidth 16) := by
  intro equal
  apply outside
  right
  rw [equal]
  cases ret <;> cases keep <;> decide

theorem storeStackOperand_frame (memory : Word → Byte) (ret short : Bool)
    (pointer : Byte) (value : Word) {address : Word} (outside : ¬ StackScratch address) :
    storeStackOperand memory (stackBase ret) pointer value short address = memory address := by
  have data (index : Byte) := StackScratch.data_separate outside ret index
  cases short <;>
    simp [storeStackOperand, Function.update_of_ne (StackScratch.pointer_separate outside ret), Function.update_of_ne (data pointer),
      Function.update_of_ne (data (pointer + 1#8))]

end ProgramProofs.Uxnmin
