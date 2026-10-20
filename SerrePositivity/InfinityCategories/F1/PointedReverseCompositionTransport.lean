module

public import SerrePositivity.InfinityCategories.F1.PointedSpaceParametrizedEquivalence
public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransportSquare

/-!
概要：反対 Kan 圏の豊穣合成を実際の pointed-space 射影の輸送族へ移す。
方針：底の同型を coslice 全体へ持ち上げ、同じ合成 prism の両端を正規化する。
規約：一点 Hom と辺のパラメーターの反転を保持し、fiber の逆同値を選ばない。
使われ方：pointed 自然性の二段輸送と Kan 値の Hom の作用を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance : ∀ A B : KanObject.{u}ᵒᵖ, KanComplex (SimplicialCategory.sHom A B) :=
  fun A B ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom B.unop A.unop))

/-- 反対 Kan nerve の一点 coslice と実際の pointed-space 全空間の同型。 -/
def reverseKanPointCosliceIso :
    sliceUnder (SSet.yonedaEquiv.symm
      (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject.{u})))) ≅
        PointedSpaceInfinity.{u} :=
  pointCoslicePostIso reverseKanNerveSpaceIso
    (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject))) ≪≫
  eqToIso (congrArg (fun z ↦ sliceUnder (SSet.yonedaEquiv.symm z))
    (reverseKanNerveSpaceIso_vertex pointKanObject))

/-- 一点 coslice の全空間の同型は元の底の同型を厳密に被覆する。 -/
lemma reverseKanPointCosliceIso_projection :
    reverseKanPointCosliceIso.hom ≫ pointedSpaceProjection =
      sliceUnderProjection (SSet.yonedaEquiv.symm
        (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject.{u})))) ≫
        reverseKanNerveSpaceIso.hom := by
  change reverseKanPointCosliceIso.hom ≫
    sliceUnderProjection (SSet.yonedaEquiv.symm (spaceInfinityVertex pointKanObject)) = _
  dsimp only [reverseKanPointCosliceIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, sliceUnder_eqToHom_projection
    (congrArg SSet.yonedaEquiv.symm (reverseKanNerveSpaceIso_vertex pointKanObject))]
  exact pointCoslicePostIso_projection _ _

/-- 反転した一点 Hom を、空間 K 上の実際の pointed fiber へ写す比較。 -/
def pointedReverseKanFiberComparison (K : KanObject.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op K) (Opposite.op pointKanObject))).op ⟶
        vertexFiber pointedSpaceProjection (spaceInfinityVertex K) :=
  vertexFiberLift pointedSpaceProjection (spaceInfinityVertex K)
    (coherentReverseSliceFiberComparison (Opposite.op K) (Opposite.op pointKanObject) ≫
      vertexFiberι _ _ ≫ reverseKanPointCosliceIso.hom) (by
        rw [Category.assoc, Category.assoc, reverseKanPointCosliceIso_projection,
          ← Category.assoc (vertexFiberι _ _) _ _, vertexFiberι_comp, SSet.const_comp,
          reverseKanNerveSpaceIso_vertex, SSet.comp_const])

/-- 元の反転した豊穣 Hom の区間族を SpaceInfinity へ移した同じ底の族。 -/
def pointedReverseKanHomInterval (K L : KanObject.{u}) :
    Δ[1] ⊗ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op L) (Opposite.op K))).op ⟶ SpaceInfinity.{u} :=
  coherentReverseHomInterval (Opposite.op L) (Opposite.op K) ≫ reverseKanNerveSpaceIso.hom

/-- 移した区間族の始点は元の Kan 空間 K。 -/
lemma pointedReverseKanHomInterval_zero (K L : KanObject.{u}) :
    prismEndpoint 0 _ ≫ pointedReverseKanHomInterval K L =
      SSet.const (spaceInfinityVertex K) := by
  rw [pointedReverseKanHomInterval, ← Category.assoc, coherentReverseHomInterval_zero,
    SSet.const_comp, reverseKanNerveSpaceIso_vertex]

/-- 移した区間族の終点は元の Kan 空間 L。 -/
lemma pointedReverseKanHomInterval_one (K L : KanObject.{u}) :
    prismEndpoint 1 _ ≫ pointedReverseKanHomInterval K L =
      SSet.const (spaceInfinityVertex L) := by
  rw [pointedReverseKanHomInterval, ← Category.assoc, coherentReverseHomInterval_one,
    SSet.const_comp, reverseKanNerveSpaceIso_vertex]

/-- 全ての一点 Hom と豊穣射に対する実際の pointed-space の合成輸送族。 -/
def pointedReverseKanCompositionTransportFamily (K L : KanObject.{u}) :
    FiberTransportFamily (b := spaceInfinityVertex L) pointedSpaceProjection
      (pointedReverseKanFiberComparison K) (pointedReverseKanHomInterval K L) where
  endpoint := coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
    (Opposite.op pointKanObject) ≫ pointedReverseKanFiberComparison L
  prism := coherentCompositionReversePrism (Opposite.op L) (Opposite.op K)
    (Opposite.op pointKanObject) ≫ reverseKanPointCosliceIso.hom
  start := by
    rw [← Category.assoc, coherentCompositionReversePrism_zero]
    rfl
  finish := by
    rw [← Category.assoc, coherentCompositionReversePrism_one]
    rfl
  over_base := by
    rw [Category.assoc, reverseKanPointCosliceIso_projection, ← Category.assoc,
      coherentCompositionReversePrism_projection, Category.assoc]
    rfl

/-- 同じ反転した一点 Hom の作用は、実際の pointed-space の普遍輸送と関手同型。 -/
def pointedReverseKanCompositionTransport_parametrizedIso (K L : KanObject.{u}) :
    FunctorIso
      (curry (coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject) ≫ pointedReverseKanFiberComparison L))
      (intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
        (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) ≫
      parametrizedFiberTransport pointedSpaceProjection
        (spaceInfinityVertex K) (spaceInfinityVertex L) ≫
      (pre (pointedReverseKanFiberComparison K)).app
        (vertexFiber pointedSpaceProjection (spaceInfinityVertex L))) :=
  (pointedReverseKanCompositionTransportFamily K L).mapIso_parametrizedSource
    pointedSpaceProjection _ _
    (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L)

/-- 動く一点 Hom と辺への同時評価でも、同じ豊穣合成が実際の対角輸送を与える。 -/
def pointedReverseKanCompositionTransport_diagonalIso
    {P : SSet.{u + 1}} (K L : KanObject.{u})
    (x : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op K) (Opposite.op pointKanObject))).op)
    (y : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op L) (Opposite.op K))).op) :
    FunctorIso
      (lift x y ≫ coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject) ≫ pointedReverseKanFiberComparison L)
      (diagonalFiberTransport pointedSpaceProjection (x ≫ pointedReverseKanFiberComparison K)
        (y ≫ intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
          (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L))) :=
  (pointedReverseKanCompositionTransportFamily K L).diagonalIso pointedSpaceProjection _ _
    (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) x y

/-- 実際の pointed fiber への反転した一点 Hom 比較は同値。 -/
lemma pointedReverseKanFiberComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (pointedReverseKanFiberComparison K) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm
    (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject.{u}))))
  let a := SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op K))
  let k := transportSquareFiberMap p pointedSpaceProjection reverseKanPointCosliceIso.hom
    reverseKanNerveSpaceIso.hom reverseKanPointCosliceIso_projection a
  have : IsIso k := transportSquareFiberMap_isIso p pointedSpaceProjection
    reverseKanPointCosliceIso reverseKanNerveSpaceIso reverseKanPointCosliceIso_projection a
  let e := asIso k ≪≫ eqToIso
    (congrArg (vertexFiber pointedSpaceProjection) (reverseKanNerveSpaceIso_vertex K))
  have he : pointedReverseKanFiberComparison K =
      coherentReverseSliceFiberComparison (Opposite.op K) (Opposite.op pointKanObject) ≫
        e.hom := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  rw [he]
  exact (coherentReverseSliceFiberComparison_homotopyEquivalence
    (Opposite.op K) (Opposite.op pointKanObject)).isQCatEquivalence.comp
      (qCatEquivalenceOfIso e).isQCatEquivalence

end SerrePositivity.InfinityCategories
