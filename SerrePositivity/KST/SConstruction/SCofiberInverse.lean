module
public import SerrePositivity.KST.SConstruction.SCofiberComparison
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection

/-! # cofiber と S 構成の交換の逆向き
概要：S_n 内の cofiber 四角形を Ar 方向へ転置して cofiber 値の gapped 図式にする。
方針：全 Ar 成分の cofiber 性で内部 Hom を持ち上げ、周囲から gapped 性を反映する。
規約：零角や押し出しの選択を変更しない。使われ方：交換の厳密な同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- S_n 内の cofiber 四角形を二重内部 Hom 内で転置する。 -/
def sCofiberRawInverse (n : ℕ) (C : SSet.{u}) :
    cofiberDiagrams (sConstruction n C) ⟶
      (ihom (arNerve n)).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom

/-- 逆向きの転置の頂点は元の S_n 値の四角形の実際の転置。 -/
lemma sCofiberRawInverse_vertex (n : ℕ) (C : SSet.{u})
    (v : (cofiberDiagrams (sConstruction n C)) _⦋0⦌) :
    (sCofiberRawInverse n C).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val ≫ (gappedSubcomplex n C).ι)) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) (sConstruction n C)).apply_symm_apply v.val
  have h := congrArg (fun w : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj
      (sConstruction n C)) _⦋0⦌ =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom.app
      (Opposite.op ⦋0⦌)
      (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι).app
        (Opposite.op ⦋0⦌) w)) hv.symm
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex
    (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val ≫ (gappedSubcomplex n C).ι))

/-- 逆転置した図式の全 Ar 成分は元の C の cofiber 四角形。 -/
lemma sCofiberRawInverse_cofiber (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (v : (cofiberDiagrams (sConstruction n C)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve n) ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
      IsCofiberDiagramVertex ((sCofiberRawInverse n C).app (Opposite.op ⦋0⦌) v) := by
  intro a
  rw [sCofiberRawInverse_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  have h := (gappedSquare_cofiber_iff_pointwise (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).1
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v) a
  exact h

/-- cofiber 条件を満たす逆転置の族を cofiber 図式値の内部 Hom へ持ち上げる。 -/
def sCofiberInverseDiagram (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    cofiberDiagrams (sConstruction n C) ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (sCofiberRawInverse n C) (sCofiberRawInverse_cofiber n C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward (arNerve n)
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex

/-- cofiber 値の持ち上げは元の二重内部 Hom の逆転置を厳密に回収する。 -/
lemma sCofiberInverseDiagram_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sCofiberInverseDiagram n C ≫
      (ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
        sCofiberRawInverse n C := by
  rw [sCofiberInverseDiagram, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

/-- 頂点の逆転置した図式の包含は元の四角形の転置。 -/
lemma sCofiberInverseDiagram_vertex_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (v : (cofiberDiagrams (sConstruction n C)) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
        ((sCofiberInverseDiagram n C).app (Opposite.op ⦋0⦌) v) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val ≫ (gappedSubcomplex n C).ι) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sCofiberInverseDiagram_ι n C) (Opposite.op ⦋0⦌)) v
  change ((ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app
    (Opposite.op ⦋0⦌) ((sCofiberInverseDiagram n C).app (Opposite.op ⦋0⦌) v) = _ at h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n)
    ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)).injective
  change ((ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
        ((sCofiberInverseDiagram n C).app (Opposite.op ⦋0⦌) v))) = _
  rw [Equiv.apply_symm_apply]
  exact h.trans (sCofiberRawInverse_vertex n C v)

/-- 逆転置した cofiber 値の図式は内部でも gapped。 -/
lemma sCofiberInverseDiagram_isGapped (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (v : (cofiberDiagrams (sConstruction n C)) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
      ((sCofiberInverseDiagram n C).app (Opposite.op ⦋0⦌) v)) := by
  apply IsGapped.of_fullSubcomplex IsCofiberDiagramVertex
  rw [sCofiberInverseDiagram_vertex_ι]
  apply (isGapped_functor_iff_pointwise _).2
  intro q
  rw [flipFamily_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val).app (Opposite.op ⦋0⦌) q)

/-- cofiber 図式と S_n の交換比較の逆向き。 -/
def sCofiberInverse (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    cofiberDiagrams (sConstruction n C) ⟶ sConstruction n (cofiberDiagrams C) :=
  gappedFamilyLift (sCofiberInverseDiagram n C) (sCofiberInverseDiagram_isGapped n C)

/-- 逆比較の包含を通すと構成した cofiber 値の Ar 図式を回収する。 -/
lemma sCofiberInverse_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sCofiberInverse n C ≫ (gappedSubcomplex n (cofiberDiagrams C)).ι =
      sCofiberInverseDiagram n C := gappedFamilyLift_ι _ _

end SerrePositivity.KST.SConstruction
