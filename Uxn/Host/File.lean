import Uxn.Uxn

namespace Uxn.Host.File

structure Handle where
  read : USize → IO ByteArray

def Handle.ofBytes (bytes : ByteArray) : IO Handle := do
  let cursor ← IO.mkRef 0
  return {
    read := fun count => do
      let start ← cursor.get
      let stop := min bytes.size (start + count.toNat)
      cursor.set stop
      return bytes.extract start stop }

/-- see File/stat* formatting -/
def stat (name : System.FilePath) (length : Nat) :
    IO { bytes : ByteArray // bytes.size = length } := do
  match ← name.metadata.toBaseIO with
  | .error _ => return fill length '!'
  | .ok metadata =>
    return if metadata.type == .dir then fill length '-'
      else formatSize length metadata.byteSize
where
  fill (length : Nat) (char : Char) : { bytes : ByteArray // bytes.size = length } :=
    ⟨⟨Array.replicate length char.toUInt8⟩,
      by simp only [ByteArray.size, Array.size_replicate]⟩

  formatSize (length : Nat) (size : UInt64) :
      { bytes : ByteArray // bytes.size = length } := Id.run do
    let digits := (Nat.toDigits 16 size.toNat).toArray
    if overflow : length < digits.size then
      return fill length '?'
    let padding := length - digits.size
    return ⟨⟨Array.ofFn fun i : Fin length =>
      if h : i.val < padding then '0'.toUInt8
      else digits[i.val - padding]'(by omega) |>.toUInt8⟩,
      by simp only [ByteArray.size, Array.size_ofFn]⟩

private def directory (path : System.FilePath) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  for entry in ← path.readDir do
    let details ← stat entry.path 4
    bytes := bytes ++ details.val ++ "\t".toUTF8 ++ entry.fileName.toUTF8 ++
      (if details.val[0]'(by simp [details.property]) == '-'.toUInt8
        then "/\n" else "\n").toUTF8
  return bytes

def Handle.open (name : System.FilePath) : IO Handle := do
  let path ← IO.FS.realPath name
  -- Varvara forbids access outside the working directory. Current uxn2 does
  -- not enforce this restriction, we follow the specification.
  -- https://wiki.xxiivv.com/site/varvara.html#file
  unless (← IO.FS.realPath ".").components.isPrefixOf path.components do
    throw (IO.userError "file outside working directory")
  match (← path.metadata).type with
  | .dir => Handle.ofBytes (← directory path)
  | .file => return { read := (← IO.FS.Handle.mk path .read).read }
  | _ => throw (IO.userError "not a regular file or directory")

end Uxn.Host.File
