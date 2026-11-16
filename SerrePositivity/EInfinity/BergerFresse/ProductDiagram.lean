module

public import SerrePositivity.EInfinity.BergerFresse.ConvolutionDiagram

/-!
# 元の全convolution積と二つの自然な射

Berger–Fresse §2.2・§3.1、M14 L22、報告 §401。
各対象で元の全次数の積を取り、元の前後合成を成分ごとに束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BergerFresse
open CategoryTheory Limits
open SerrePositivity.Cosimplicial (CosimplicialAlgebra)
variable (A : Type u) [CommRing A]

/-- 元の全次数のconvolution積の関手（BF §3.1）。 -/
def convolutionProductFunctor : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra :=
  Functor.pi' (fun q : ℕ => convolutionAt A q q) ⋙ Limits.Pi.functor ℕ

/-- 元の全単体射にわたるconvolution積の関手（BF §3.1）。 -/
def convolutionArrowProductFunctor : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra :=
  Functor.pi' (fun α : SimplexMorphismIndex => convolutionAt A α.1 α.2.1) ⋙
    Limits.Pi.functor SimplexMorphismIndex

/-- 同じ元の次数の積への射影（BF §3.1）。 -/
def convolutionProductProjection (q : ℕ) : convolutionProductFunctor A ⟶ convolutionAt A q q :=
  Functor.whiskerLeft (Functor.pi' (fun q : ℕ => convolutionAt A q q)) (Limits.Pi.functorπ q) ≫
    (Functor.pi'CompEval (fun q : ℕ => convolutionAt A q q) q).hom

/-- 同じ対象ごとの積の普遍性で自然な成分を束ねる（BF §3.1）。 -/
def convolutionProductLift
    (F : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra)
    (φ : ∀ α : SimplexMorphismIndex, F ⟶ convolutionAt A α.1 α.2.1) :
    F ⟶ convolutionArrowProductFunctor A where
  app X := Pi.lift (fun i => (φ i).app X)
  naturality := by
    intro X Y f
    apply Pi.hom_ext
    intro i
    dsimp only [convolutionArrowProductFunctor, Functor.comp_map, Functor.pi', Limits.Pi.functor]
    simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Pi.map_π]
    exact (φ i).naturality f

/-- 元の全単体射の後合成の積（BF §3.1）。 -/
def post : convolutionProductFunctor A ⟶ convolutionArrowProductFunctor A :=
  convolutionProductLift A _ (fun α : SimplexMorphismIndex =>
    convolutionProductProjection A α.1 ≫ postAt A α.2.2)

/-- 元の全単体射の前合成の積（BF §3.1）。 -/
def pre : convolutionProductFunctor A ⟶ convolutionArrowProductFunctor A :=
  convolutionProductLift A _ (fun α : SimplexMorphismIndex =>
    convolutionProductProjection A α.2.1 ≫ preAt A α.2.2)

/-- L22：元の後合成の積の自然性（BF §3.1）。 -/
lemma post_naturality {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    (convolutionProductFunctor A).map f ≫ (post A).app Y =
      (post A).app X ≫ (convolutionArrowProductFunctor A).map f :=
  (post A).naturality f

/-- L22：元の前合成の積の自然性（BF §3.1）。 -/
lemma pre_naturality {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    (convolutionProductFunctor A).map f ≫ (pre A).app Y =
      (pre A).app X ≫ (convolutionArrowProductFunctor A).map f :=
  (pre A).naturality f

end SerrePositivity.EInfinity.BergerFresse
