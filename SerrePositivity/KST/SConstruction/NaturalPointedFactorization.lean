module
public import SerrePositivity.KST.Spectra.PointedFactorization
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import Mathlib.CategoryTheory.Comma.Arrow
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-! # 点つき自然変換の関手的な単射分解
概要：L9 の点つき射の分解を、任意の添字圏上の自然変換へ適用する。
方針：底の射の Arrow 図式に小対象論法の中間対象の関手を適用し、基点を左因子で写す。
規約：両側の Kan 性は分解の定義に不要。使われ方：S₁ 比較と構造射の Kan な単射模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：点つき自然変換の底の射を Arrow 図式にまとめる。
方針：自然性の四角形を Arrow の射とする。
規約：添字の対象・射の宇宙は独立。使われ方：関手的因子分解への入力。 -/
def pointedTransformationArrows {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : T ⥤ Arrow SSet.{u} where
  obj X := Arrow.mk (α.app X).right
  map {X Y} f := Arrow.homMk
    (f := Arrow.mk (α.app X).right) (g := Arrow.mk (α.app Y).right)
    (F.map f).right (G.map f).right (by
      change (F.map f).right ≫ (α.app Y).right = (α.app X).right ≫ (G.map f).right
      exact congrArg Under.Hom.right (α.naturality f))
  map_id X := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext <;> simp

/-- 概要：点つき自然変換を分解した中間対象の関手。
方針：底の中間対象の関手と左因子の自然性で基点を保持する。
規約：L9 の既存の中間対象を変更しない。使われ方：自然な Kan 比較模型。 -/
def pointedTransformationMiddle {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : T ⥤ PointedSimplicialSet.{u} where
  obj X := Spectra.PointedFactorization.middle (α.app X)
  map {X Y} f := Under.homMk
    (Spectra.PointedFactorization.factorization.Z.map ((pointedTransformationArrows α).map f)) (by
      have hi := Spectra.PointedFactorization.factorization.i.naturality
        ((pointedTransformationArrows α).map f)
      change (F.map f).right ≫ Spectra.PointedFactorization.factorization.i.app
          (Arrow.mk (α.app Y).right) =
        Spectra.PointedFactorization.factorization.i.app (Arrow.mk (α.app X).right) ≫
          Spectra.PointedFactorization.factorization.Z.map ((pointedTransformationArrows α).map f) at hi
      change ((F.obj X).hom ≫ Spectra.PointedFactorization.factorization.i.app
        (Arrow.mk (α.app X).right)) ≫ _ =
        (F.obj Y).hom ≫ Spectra.PointedFactorization.factorization.i.app (Arrow.mk (α.app Y).right)
      rw [Category.assoc, ← hi, ← Category.assoc, Under.w])
  map_id X := by
    apply Under.UnderMorphism.ext
    change Spectra.PointedFactorization.factorization.Z.map
      ((pointedTransformationArrows α).map (𝟙 X)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply Under.UnderMorphism.ext
    change Spectra.PointedFactorization.factorization.Z.map
      ((pointedTransformationArrows α).map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- 概要：自然変換の分解の左側の自然変換。
方針：各成分に L9 の左因子を置く。
規約：底の射は単射。使われ方：自然な単射模型。 -/
def pointedTransformationLeft {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : F ⟶ pointedTransformationMiddle α where
  app X := Spectra.PointedFactorization.left (α.app X)
  naturality {X Y} f := by
    apply Under.UnderMorphism.ext
    exact Spectra.PointedFactorization.factorization.i.naturality
      ((pointedTransformationArrows α).map f)

/-- 概要：自然変換の分解の右側の自然変換。
方針：各成分に L9 の右因子を置く。
規約：底の射は全単射に対する右持ち上げ性を持つ。使われ方：元の Kan 模型との比較。 -/
def pointedTransformationRight {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : pointedTransformationMiddle α ⟶ G where
  app X := Spectra.PointedFactorization.right (α.app X)
  naturality {X Y} f := by
    apply Under.UnderMorphism.ext
    exact Spectra.PointedFactorization.factorization.p.naturality
      ((pointedTransformationArrows α).map f)

/-- 概要：自然な二つの因子の合成は元の自然変換。
方針：各成分の L9 の分解の式を使う。
規約：厳密な等号。使われ方：構造射との比較図式。 -/
lemma pointedTransformation_fac {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) :
    pointedTransformationLeft α ≫ pointedTransformationRight α = α := by
  apply NatTrans.ext
  funext X
  exact Spectra.PointedFactorization.fac (α.app X)

/-- 概要：自然な分解の左因子の各成分は単射。
方針：L9 の左因子の単射性。
規約：底の単体集合の射について。使われ方：構造射の単射化の入力。 -/
instance pointedTransformationLeft_mono {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) :
    Mono ((pointedTransformationLeft α).app X).right :=
  Spectra.PointedFactorization.left_mono (α.app X)

/-- 概要：自然な分解の右因子の各成分は trivial Kan fibration。
方針：L9 の全単射に対する右持ち上げ性を使う。
規約：源・標的の Kan 性を要求しない。使われ方：比較射の充填性。 -/
instance pointedTransformationRight_trivialKanFibration {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pointedTransformationRight α).app X).right :=
  ⟨Spectra.PointedFactorization.right_rlp (α.app X)⟩

/-- 概要：標的が Kan なら自然な中間対象も Kan。
方針：L9 の右因子の fibration 性と標的の Kan 性を使う。
規約：各入力についての条件。使われ方：Kan な比較模型。 -/
instance pointedTransformationMiddle_kanComplex {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) [KanComplex (G.obj X).right] :
    KanComplex ((pointedTransformationMiddle α).obj X).right :=
  Spectra.PointedFactorization.middle_kanComplex (α.app X)

/-- 概要：Kan な標的への自然な分解の右因子は全基点 π_* 同型。
方針：L9 の全単射に対する右持ち上げ性の比較を使う。
規約：各入力での主張。使われ方：中間 Kan 模型との同値比較。 -/
lemma pointedTransformationRight_piIsomorphism {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T) [KanComplex (G.obj X).right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((pointedTransformationRight α).app X).right :=
  Spectra.PointedFactorization.right_piIsomorphism (α.app X)

/-- 概要：元の比較が π_* 同型なら単射な左因子も π_* 同型。
方針：合成が元の比較である式と右因子の π_* 同型性で打ち消す。
規約：両端は Kan。使われ方：S₁ 比較の自然な単射模型。 -/
lemma pointedTransformationLeft_piIsomorphism {T : Type v} [Category.{w} T]
    {F G : T ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) (X : T)
    [KanComplex (F.obj X).right] [KanComplex (G.obj X).right]
    (hα : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (α.app X).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((pointedTransformationLeft α).app X).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((pointedTransformationRight α).app X).right) _
    (pointedTransformationRight_piIsomorphism α X)
  have h := congrArg Under.Hom.right (Spectra.PointedFactorization.fac (α.app X))
  change ((pointedTransformationLeft α).app X).right ≫
    ((pointedTransformationRight α).app X).right = (α.app X).right at h
  rw [h]
  exact hα

end SerrePositivity.KST.SConstruction
