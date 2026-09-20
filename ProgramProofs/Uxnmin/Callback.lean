import ProgramProofs.Uxnmin.Loader.Tactics
import ProgramProofs.Uxnmin.Boundary
import ProgramProofs.Uxnmin.RepresentationPC

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
theorem pair_zero (a b : BitVec 8) : (b ||| a = 0#8) ↔ (a ++ b = 0#16) := by
  rw [BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨low, high⟩
    rw [high, low]
    rfl
  · intro same
    constructor
    · have low := congrArg (fun value : BitVec 16 => value.setWidth 8) same
      rw [BitVec.setWidth_append_eq_right] at low
      exact low
    · have high := congrArg (fun value : BitVec 16 => (value >>> 8).setWidth 8) same
      rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left] at high
      exact high
private theorem pair_high (a b : BitVec 8) : ((a ++ b) >>> 8).setWidth 8 = a := by
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
private theorem pair_low (a b : BitVec 8) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right

open Uxn Uxn.Host ProgramProofs.Host

/-- A cleared guest vector skips callback execution and reaches the callback BRK. -/
theorem callback_skip (ram : Word → Byte) (code : CodeImage ram)
    (w r : Byte → Byte) (host : Uxn.Host.State) (after : Console)
    (zero : ram 0x175 ++ ram 0x176 = 0#16) :
    ∃ final : Uxn.Host.State, PureReaches {host with
        vm := machine ram 0x174 ⟨w, 0⟩ ⟨r, 0⟩,
        control := .evaluating (.console after)} final ∧
      final = {host with
        vm := machine ram 0x17c final.vm.mem.wstk final.vm.mem.rstk,
        control := .evaluating (.console after)} ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have zero : ram 0x176#16 ||| ram 0x175#16 = 0#8 := (pair_zero _ _).mpr zero
  have c174 : ram 0x174#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c177 : ram 0x177#16 = 0x9d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c178 : ram 0x178#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c179 : ram 0x179#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17a : ram 0x17a#16 = 0x2#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17b : ram 0x17b#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17c : ram 0x17c#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  host_steps 4 [c174, c177, c178, c179, c17a, c17b, c17c, zero, Function.update_apply]
  exact ⟨_, .refl _, rfl, rfl, rfl⟩

/-- A nonzero callback vector refreshes input literals and enters guest evaluation. -/
theorem callback_enter (ram : Word → Byte) (code : CodeImage ram)
    (w r : Byte → Byte) (host : Uxn.Host.State) (after : Console)
    (zero : ram 0x175 ++ ram 0x176 ≠ 0#16) :
    ∃ final : Uxn.Host.State, PureReaches {host with
        vm := machine ram 0x174 ⟨w, 0⟩ ⟨r, 0⟩,
        control := .evaluating (.console after)} final ∧
      final.control = .evaluating (.console after) ∧
      final.ports = host.ports ∧ final.consoleVector = host.consoleVector ∧
      final.vm.pc = 0x16d ∧ final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 2 ∧
      final.vm.mem.rstk.data 0 ++ final.vm.mem.rstk.data 1 = 0x18f#16 ∧
      final.vm.mem.ram = Function.update (Function.update
        (Function.update (Function.update ram 0x199 (host.read Port.Console.read))
          0x1a4 (host.read Port.Console.type)) 0x45 (ram 0x175)) 0x46 (ram 0x176) := by
  have zero : ram 0x176#16 ||| ram 0x175#16 ≠ 0#8 := fun same => zero ((pair_zero _ _).mp same)
  have c174 : ram 0x174#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c177 : ram 0x177#16 = 0x9d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c178 : ram 0x178#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c179 : ram 0x179#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17a : ram 0x17a#16 = 0x2#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17b : ram 0x17b#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17c : ram 0x17c#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17d : ram 0x17d#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17e : ram 0x17e#16 = 0x12#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c17f : ram 0x17f#16 = 0x16#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c180 : ram 0x180#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c181 : ram 0x181#16 = 0x16#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c182 : ram 0x182#16 = 0x13#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c183 : ram 0x183#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c184 : ram 0x184#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c185 : ram 0x185#16 = 0x16#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c186 : ram 0x186#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c187 : ram 0x187#16 = 0x1b#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c188 : ram 0x188#16 = 0x13#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c189 : ram 0x189#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c18a : ram 0x18a#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c18b : ram 0x18b#16 = 0xfc#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c18c : ram 0x18c#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c18d : ram 0x18d#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c18e : ram 0x18e#16 = 0xde#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c288 : ram 0x288#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c289 : ram 0x289#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c28a : ram 0x28a#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have c28b : ram 0x28b#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  host_steps 16 [c174, c177, c178, c179, c17a, c17b, c17c, c17d, c17e, c17f, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c18a, c18b, c18c, c18d, c18e, c288, c289, c28a, c28b, zero, Function.update_apply]
  refine ⟨_, .refl _, ?_⟩
  simp [host_read, Port.Console.read, Port.Console.type, pair_high, pair_low]

end ProgramProofs.Uxnmin.Model
