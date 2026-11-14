module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# 向き付き prism の圏と平坦な射

BS 著者版 Definition 3.2 のうち、単項 prism に生成元を選んだ場合の圏。
射は生成元そのものを保存する必要はなく、既存の δ 対の射を用いる。
平坦性は (p,d) 完全平坦性。相対 prismatic site の被覆の記法を統一する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze

/-- BS 著者版 Definition 3.2 の向き付き prism の対象。
台環とその向き付き prism 構造を束ねる。一般の非単項 prism は含めない。 -/
structure OrientedPrismCat (p : ℕ) [Fact p.Prime] where
  /-- 台の可換環。 -/
  carrier : CommRingCat.{u}
  /-- 選択した生成元を持つ prism 構造。 -/
  prism : OrientedPrism p carrier

instance {p : ℕ} [Fact p.Prime] : Category (OrientedPrismCat.{u} p) where
  Hom X Y := OrientedPrism.Hom X.prism Y.prism
  id X := OrientedPrism.Hom.id X.prism
  comp f g := g.comp f
  id_comp f := OrientedPrism.Hom.comp_id f
  comp_id f := OrientedPrism.Hom.id_comp f
  assoc f g h := (OrientedPrism.Hom.comp_assoc h g f).symm

namespace OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type u} [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- BS 著者版 Definition 3.2 の平坦な prism 射。
台の環射が与える加群構造で (p,d) 完全平坦性を判定する。
通常の平坦性への置換ではなく、prismatic site の被覆に使う条件。 -/
def IsFlat (f : Hom P Q) : Prop :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  IsCompletelyFlat (Ideal.span {(p : A), P.generator}) B

/-- BS 著者版 Definition 3.2 の忠実平坦な prism 射。
(p,d) 完全忠実平坦性を台の環射に対して課す。 -/
def IsFaithfullyFlat (f : Hom P Q) : Prop :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  IsCompletelyFaithfullyFlat (Ideal.span {(p : A), P.generator}) B

/-- 忠実平坦な prism 射は平坦。完全忠実平坦性の第一条件を取り出す。 -/
theorem IsFaithfullyFlat.isFlat {f : Hom P Q} (h : f.IsFaithfullyFlat) : f.IsFlat := h.1

end OrientedPrism.Hom
end SerrePositivity.BhattScholze
