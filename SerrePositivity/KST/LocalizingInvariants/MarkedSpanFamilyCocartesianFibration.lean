module
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyCocartesianEdge

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanPostcomposition
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration

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
    (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) : CocartesianFibration (markedSpanFamilyProjection X W x) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro v b hb
    obtain ⟨G, hG₀, hGt, hGs, hGa, _hGl⟩ := exists_markedSpanPostcomposition W v.val b hb
    have hv : (markedSpanSource X W).app (Opposite.op ⦋0⦌) v.val = x := by
      simpa only [PinchedHom.constant_zero] using v.property
    have hs : G ≫ markedSpanSource X W = SSet.const x :=
      hGs.trans (congrArg SSet.const hv)
    let F := vertexFiberLift (markedSpanSource X W) x G hs
    have hF : F ≫ vertexFiberι (markedSpanSource X W) x = G := vertexFiberLift_ι _ _ _ _
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
          PinchedHom.constant v.val 0 at hh
        rw [pinchedConstant_zero] at hh
        exact hh
      apply SSet.yonedaEquiv.injective
      calc
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ F) =
            (markedSpanFamily X W x).δ 1 (SSet.yonedaEquiv F) :=
          (SSet.yonedaEquiv_naturality (SimplexCategory.δ (1 : Fin 2)) F).symm
        _ = F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := intervalMap_source F
        _ = v := hf₀
        _ = _ := (SSet.yonedaEquiv.apply_symm_apply v).symm
    · change (F ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanTarget X W = b
      rw [hF]
      exact hGt
    · have hFa : F ≫ markedSpanFamilyApex X W x =
          SSet.const ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v.val) := by
        change (F ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanApex X W = _
        rw [hF]
        exact hGa
      apply isCocartesianEdge_markedSpanFamilyProjection_of_apex
      have hi := isEquivalencePathVertex_const
        ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v.val)
      unfold IsEquivalencePathVertex at hi
      rw [intervalFunctorVertexEdge_functorVertex] at hi
      have he : ((edgeOfSimplex (SSet.yonedaEquiv F)).map
          ((truncation 2).map (markedSpanFamilyApex X W x))).edge =
          PinchedHom.constant ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v.val) 1 := by
        change (markedSpanFamilyApex X W x).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
        rw [← SSet.yonedaEquiv_comp, hFa]
        rfl
      exact (isInvertibleEdge_congr he).mpr hi

end SerrePositivity.KST.LocalizingInvariants
