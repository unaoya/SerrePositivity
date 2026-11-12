module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleFactor

/-!
概要：実零角への任意の完全 Hom の全像を同じ固定 ν の零合成空間へ置く。
方針：元の実上辺で後合成し、実零角の全零性と完全性を使う。
規約：元の零角・元上辺・全高次 Hom を保持する。
使われ方：零角を含む混合比較面の全境界充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma zeroCornerWhiskerVertex {X Y Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Z : SSet.{u})).ι.app (Opposite.op ⦋0⦌)
      ((eHomWhiskerLeft (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) SSet X g).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) X Y f)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv X Z (f ≫ g) := by
  rfl

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))
local notation "t" => dgKInputNuMap R
  (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))

/-- 概要：同じ実零角への全 Hom の元上辺による後合成。
方針：元の豊穣後合成作用を使う。
規約：全高次パラメータを保持。使われ方：零角混合面の元 Hom。 -/
def dgOdotMilnorNuZeroCornerNullHom :
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z) ⟶
      SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B) :=
  eHomWhiskerLeft (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) SSet (K) (t)

/-- 概要：元上辺で後合成した完全射は全対象を零対象へ送る。
方針：元の実零角の全零性と元上辺の完全性を使う。
規約：零角への任意の実完全射。使われ方：全 Hom 像の零成分判定。 -/
lemma dgOdotMilnorNuZeroCornerComposite_zero (f : (K) ⟶ (Z))
    (x : (K).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((f.hom ≫ (t).hom).app (Opposite.op ⦋0⦌) x) := by
  exact @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ (t).hom (t).isExact _
    (dgFixedNullInput_isZeroCategory R _ _)

/-- 概要：実零角を経由する全 Hom 像の全頂点は同じ終関手成分。
方針：任意の元 Hom 頂点を完全射へ戻し、点ごとの全零性を使う。
規約：元 Hom 頂点を選び直さない。使われ方：全零成分への制限。 -/
lemma dgOdotMilnorNuZeroCornerNullHom_vertex_isTerminal
    (a : (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuZeroCornerNullHom R d ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) a) := by
  let f : (K) ⟶ (Z) := (SimplicialCategory.homEquiv'
    (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)).symm a
  have ha : SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z) f = a :=
    Equiv.apply_symm_apply _ _
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (f ≫ (t))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f.hom ≫ (t).hom))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
      (fun x => (dgOdotMilnorNuZeroCornerComposite_zero R d f x).2)
  have hv := zeroCornerWhiskerVertex f (t)
  exact ha ▸ hv.symm ▸ ht

/-- 概要：実零角を経由する全 Hom を同じ固定 ν の零合成空間へ置く。
方針：全頂点の終関手性で元の後合成写像を制限する。
規約：元の全高次単体を保持。使われ方：零角混合面の全相対充填。 -/
def dgOdotMilnorNuZeroCornerNullFactor :
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z) ⟶
      DGOdotMilnorNuNullCoherenceSpace R d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (dgOdotMilnorNuZeroCornerNullHom R d ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι)
    (dgOdotMilnorNuZeroCornerNullHom_vertex_isTerminal R d)

/-- 概要：零角の全零因子分解は同じ元後合成 Hom を厳密に回収する。
方針：元 core 包含の単射性を使う。
規約：全単体の等号。使われ方：指定零角の全図式比較。 -/
lemma dgOdotMilnorNuZeroCornerNullFactor_hom (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    dgOdotMilnorNuZeroCornerNullFactor R d ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuZeroCornerNullHom R d := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).mp
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => dgOdotMilnorNuZeroCornerNullFactor R d ≫ f)
      (dgOdotMilnorNuNullCoherenceHom_inclusion R d h))

end SerrePositivity.KST.SConstruction
