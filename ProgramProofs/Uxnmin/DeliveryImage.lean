import ProgramProofs.Uxnmin.Callback

set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

def deliver (host : Uxn.Host.State) (value kind : Byte) : Uxn.Host.State :=
  (host.write Port.Console.read value).write Port.Console.type kind

theorem ConsoleImage.deliver {guest outer : Uxn.Host.State} (image : ConsoleImage guest outer)
    (value kind : Byte) : ConsoleImage (deliver guest value kind) (deliver outer value kind) := by
  refine ⟨image.core, ?_, image.vector, ?_, image.working, image.returning, image.outerVector⟩
  · intro port input type
    change outer.vm.mem.ram (0x759 + port.setWidth 16) =
      ((guest.write Port.Console.read value).write Port.Console.type kind).read port
    simpa only [host_write_read, if_neg input, if_neg type] using image.ports port input type
  · simpa [ProgramProofs.Uxnmin.Model.deliver, host_write_read, Port.System.state, Port.Console.read, Port.Console.type] using image.system

theorem Represents.writeInput {guest outer : Uxn.State} (rep : Represents guest outer)
    (address : Word) (value : Byte) (available : address = 0x199 ∨ address = 0x1a4) :
    Represents guest {outer with mem.ram := Function.update outer.mem.ram address value} := by
  constructor
  · apply rep.code.write
    exact .inr (.inr (by rcases available with rfl | rfl <;> simp [MutableCode]))
  · intro location confined
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.ram location confined
    · rcases available with rfl | rfl <;> dsimp [relocate, ProgramProofs.Uxnmin.ramSize] at * <;> bv_omega
  · intro ret index
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.stackData ret index
    · rcases available with rfl | rfl <;> cases ret <;> dsimp [stackBase] <;> bv_omega
  · intro ret
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.stackPointer ret
    · rcases available with rfl | rfl <;> cases ret <;> dsimp [stackBase] <;> bv_omega
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.pcHigh
    · rcases available with rfl | rfl <;> decide
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.pcLow
    · rcases available with rfl | rfl <;> decide

theorem callback_image {guest outer final : Uxn.Host.State} (image : ConsoleImage guest outer)
    (last : Bool)
    (input : outer.read Port.Console.read = guest.read Port.Console.read)
    (kind : outer.read Port.Console.type = guest.read Port.Console.type)
    (control : final.control = .evaluating (.console (remaining last)))
    (ports : final.ports = outer.ports) (vector : final.consoleVector = outer.consoleVector)
    (pc : final.vm.pc = 0x16d) (working : final.vm.mem.wstk.ptr = 0)
    (returning : final.vm.mem.rstk.ptr = 2)
    (frame : final.vm.mem.rstk.data 0 ++ final.vm.mem.rstk.data 1 = 0x18f#16)
    (memory : final.vm.mem.ram = Function.update (Function.update
      (Function.update (Function.update outer.vm.mem.ram 0x199 (outer.read Port.Console.read))
        0x1a4 (outer.read Port.Console.type)) 0x45 (outer.vm.mem.ram 0x175)) 0x46 (outer.vm.mem.ram 0x176)) :
    Evaluation (.callback last)
      {guest with vm.pc := guest.consoleVector, control := .evaluating (.console (remaining last))} final := by
  have high : (guest.consoleVector >>> 8).setWidth 8 = outer.vm.mem.ram 0x175 := by
    rw [← image.vector, BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have low : guest.consoleVector.setWidth 8 = outer.vm.mem.ram 0x176 := by
    rw [← image.vector, BitVec.setWidth_append_eq_right]
  refine ⟨?_, ?_, ?_, rfl, control, vector.trans image.outerVector, returning, frame, by intro h; cases h⟩
  · refine ⟨?_, pc, working, by rw [returning]; decide⟩
    apply ((Represents.writeInput (Represents.writeInput image.core _ _ (.inl rfl)) _ _ (.inr rfl)).setPC guest.consoleVector).transport
    simpa only [high, low] using memory
  · constructor
    · intro port inputPort typePort
      rw [memory]
      repeat rw [Function.update_of_ne (by bv_omega)]
      exact image.ports port inputPort typePort
    · simpa [memory, Function.update_apply, Uxn.Host.State.read] using input
    · simpa [memory, Function.update_apply, Uxn.Host.State.read] using kind
    · simpa [memory, Function.update_apply] using image.vector
  · change final.ports.get Port.System.state.toFin = guest.ports.get Port.System.state.toFin
    rw [ports]
    exact image.system

end ProgramProofs.Uxnmin.Model
