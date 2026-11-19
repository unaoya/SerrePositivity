module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.MarkedSpanFamilyCocartesianEdge

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

/-!
概要：第一終点を固定した分母付き span の第二終点射影は cocartesian fibration。
方針：第一脚を固定する実持ち上げを構成し、始点成分の恒等性から外ホーン判定を適用する。
規約：分母集合は任意。使われ方：分数の族の fiber ごとの亜群化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

instance markedSpanFamilyProjection_cocartesianFibration (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro v b hb
    obtain ⟨G, hG₀, hGt, hGs, hGa, _hGl⟩ := exists_markedSpanPostcomposition W v.val b hb
    have hv : (markedSpanSource X W).app (Opposite.op ⦋0⦌) v.val = x := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using v.property
    have hs : G ≫ markedSpanSource X W = SSet.const x :=
      hGs.trans (congrArg SSet.const hv)
    let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (markedSpanSource X W) x G hs
    have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x = G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
    refine ⟨F, ?_, ?_, ?_⟩
    · have hf₀ : F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = v := by
        apply Subtype.ext
        have hh := congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ markedSpans X W =>
          k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) hG₀
        simp only [NatTrans.comp_app_apply] at hh
        have hd : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
              stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
        rw [hd] at hh
        change G.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v.val 0 at hh
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hh
        exact hh
      apply SSet.yonedaEquiv.injective
      calc
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ F) =
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x).δ 1 (SSet.yonedaEquiv F) :=
          (SSet.yonedaEquiv_naturality (SimplexCategory.δ (1 : Fin 2)) F).symm
        _ = F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := intervalMap_source F
        _ = v := hf₀
        _ = _ := (SSet.yonedaEquiv.apply_symm_apply v).symm
    · change (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanTarget X W = b
      rw [hF]
      exact hGt
    · have hFa : F ≫ markedSpanFamilyApex X W x =
          SSet.const ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v.val) := by
        change (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanApex X W = _
        rw [hF]
        exact hGa
      apply isCocartesianEdge_markedSpanFamilyProjection_of_apex
      have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const
        ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v.val)
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hi
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
      have he : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv F)).map
          ((truncation 2).map (markedSpanFamilyApex X W x))).edge =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v.val) 1 := by
        change (markedSpanFamilyApex X W x).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
        rw [← SSet.yonedaEquiv_comp, hFa]
        rfl
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hi

end SerrePositivity.KST.LocalizingInvariants
