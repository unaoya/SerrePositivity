module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.ConvolutionDiagram

/-!
模型。文献の定義との比較は後で
# 元の全convolution積と二つの自然な射

Berger–Fresse §2.2・§3.1、M14 L22、報告 §401。
各対象で元の全次数の積を取り、元の前後合成を成分ごとに束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.Cosimplicial (CosimplicialAlgebra)
variable (A : Type u) [CommRing A]

/-- 元の全次数のconvolution積の関手（BF §3.1）。 -/
def convolutionProductFunctor : CosimplicialAlgebra A ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  Functor.pi' (fun q : ℕ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q q) ⋙ Limits.Pi.functor ℕ

/-- 元の全単体射にわたるconvolution積の関手（BF §3.1）。 -/
def convolutionArrowProductFunctor : CosimplicialAlgebra A ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  Functor.pi' (fun α : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.SimplexMorphismIndex => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A α.1 α.2.1) ⋙
    Limits.Pi.functor _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.SimplexMorphismIndex

/-- 同じ元の次数の積への射影（BF §3.1）。 -/
def convolutionProductProjection (q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductFunctor A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q q :=
  Functor.whiskerLeft (Functor.pi' (fun q : ℕ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q q)) (Limits.Pi.functorπ q) ≫
    (Functor.pi'CompEval (fun q : ℕ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q q) q).hom

/-- 同じ対象ごとの積の普遍性で自然な成分を束ねる（BF §3.1）。 -/
def convolutionProductLift
    (F : CosimplicialAlgebra A ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (φ : ∀ α : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.SimplexMorphismIndex, F ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A α.1 α.2.1) :
    F ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionArrowProductFunctor A where
  app X := Pi.lift (fun i => (φ i).app X)
  naturality := by
    intro X Y f
    apply Pi.hom_ext
    intro i
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionArrowProductFunctor, Functor.comp_map, Functor.pi', Limits.Pi.functor]
    simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Pi.map_π]
    exact (φ i).naturality f

/-- 元の全単体射の後合成の積（BF §3.1）。 -/
def post : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductFunctor A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionArrowProductFunctor A :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductLift A _ (fun α : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.SimplexMorphismIndex =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductProjection A α.1 ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.postAt A α.2.2)

/-- 元の全単体射の前合成の積（BF §3.1）。 -/
def pre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductFunctor A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionArrowProductFunctor A :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductLift A _ (fun α : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.SimplexMorphismIndex =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductProjection A α.2.1 ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.preAt A α.2.2)

/-- L22：元の後合成の積の自然性（BF §3.1）。 -/
lemma post_naturality {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductFunctor A).map f ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.post A).app Y =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.post A).app X ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionArrowProductFunctor A).map f :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.post A).naturality f

/-- L22：元の前合成の積の自然性（BF §3.1）。 -/
lemma pre_naturality {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionProductFunctor A).map f ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.pre A).app Y =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.pre A).app X ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionArrowProductFunctor A).map f :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.pre A).naturality f

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse
