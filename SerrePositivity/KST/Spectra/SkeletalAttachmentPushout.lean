module

public import SerrePositivity.KST.Spectra.SkeletalCellAttachment

/-!
概要：隣り合う骨格のセルを付け加える実際の pushout 正方形。
方針：Mathlib の単射の相対セル分解を通常の骨格の同型で移す。
規約：セルの添字は cellEquiv で非退化単体へ移せる。
使われ方：Goerss–Jardine VIII §1。骨格の相対 cofiber のセルごとの表示。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SSet.relativeCellComplexOfMono

/-- 概要：d セルの境界の余積から低い骨格への貼り付け射。
方針：相対セル分解の貼り付け射を骨格の同型で移す。
規約：低い骨格は次元 d 未満。
使われ方：Goerss–Jardine VIII §1。セルの境界の構造写像。 -/
def attachingMap (K : SSet.{u}) (d : ℕ) :
    sigmaBoundary (K.skeleton d).ι d ⟶ (K.skeleton d : SSet.{u}) :=
  t (K.skeleton d).ι d ≫ (Subcomplex.eqToIso (lower_eq K d)).hom

/-- 概要：d 単体の余積から一段高い骨格への特徴射。
方針：相対セル分解の単体の特徴射を骨格の同型で移す。
規約：d 次元の単体をすべて含む骨格へ写す。
使われ方：Goerss–Jardine VIII §1。新しいセルの具体的な射。 -/
def characteristicMap (K : SSet.{u}) (d : ℕ) :
    sigmaStdSimplex (K.skeleton d).ι d ⟶ (K.skeleton (d + 1) : SSet.{u}) :=
  b (K.skeleton d).ι d ≫ (Subcomplex.eqToIso (upper_eq K d)).hom

/-- 概要：d 次元の非退化単体を境界で貼ると一段高い骨格を得る。
方針：単射の相対セル分解の pushout を通常の二つの骨格へ同型で移す。
規約：左辺は d 単体の境界包含の余積。
使われ方：Goerss–Jardine VIII §1。骨格の tower fiber のセル分解。 -/
theorem isPushout (K : SSet.{u}) (d : ℕ) :
    IsPushout (attachingMap K d) (l (K.skeleton d).ι d)
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))
      (characteristicMap K d) := by
  refine (SSet.relativeCellComplexOfMono.isPushout (K.skeleton d).ι d).of_iso
    (Iso.refl _) (Subcomplex.eqToIso (lower_eq K d))
      (Iso.refl _) (Subcomplex.eqToIso (upper_eq K d)) ?_ ?_ ?_ ?_
  · simp [attachingMap]
  · simp
  · rfl
  · simp [characteristicMap]

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
