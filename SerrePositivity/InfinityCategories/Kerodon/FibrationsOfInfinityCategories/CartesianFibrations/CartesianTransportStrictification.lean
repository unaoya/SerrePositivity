module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VerticalInvertibleLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianPreservation

/-!
概要：標的で指定した cartesian な辺へ終点指定の cartesian 輸送の像を厳密化する。
方針：二つの輸送の比較三角形の垂直な可逆辺を持ち上げ、内ホーンを充填する。
規約：対象の射は inner fibration で、cartesian 辺を保ち、各 fiber で可逆辺を持ち上げる。
使われ方：全空間の相対比較の標的で整合する cartesian 輸送を構成する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：標的の cartesian な辺を指定終点から cartesian な辺へ厳密に持ち上げられる。
方針：元の輸送の像と指定辺を比較し、可逆な第一辺を fiber 内で持ち上げて三角形を充填する。
規約：p は cartesian fibration、r と f は inner fibration。
使われ方：引き戻しの二つの輸送の像を厳密に合わせる。 -/
lemma exists_kanCartesianTransport_over_cartesianEdge {X Z C : SSet.{u}}
    [Quasicategory X] [Quasicategory Z] [Quasicategory C]
    (p : X ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] (r : Z ⟶ C) [InnerFibration r]
    (f : X ⟶ Z) [InnerFibration f] (hf : f ≫ r = p)
    (hpres : ∀ a : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p a →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r (f.app (Opposite.op ⦋1⦌) a))
    (hlift : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c))
    (x : X _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r (SSet.yonedaEquiv e))
    (ht : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x)) :
    ∃ a : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ (0 : Fin 2) ≫ a = SSet.yonedaEquiv.symm x ∧ a ≫ f = e ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv a) := by
  have hb : stdSimplex.δ (0 : Fin 2) ≫ (e ≫ r) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ht, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm
      (ConcreteCategory.congr_hom (NatTrans.congr_app hf (Opposite.op ⦋0⦌)) x)
  obtain ⟨a, hat, hap, hac⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration.mem (p := p) |>.2 x (e ≫ r) hb
  have haf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r (SSet.yonedaEquiv (a ≫ f)) := by
    rw [SSet.yonedaEquiv_comp]
    exact hpres _ hac
  have hbase : e ≫ r = (a ≫ f) ≫ r := by rw [Category.assoc, hf, hap]
  have hend : stdSimplex.δ (0 : Fin 2) ≫ e = stdSimplex.δ (0 : Fin 2) ≫ (a ≫ f) := by
    rw [← Category.assoc, hat, SSet.yonedaEquiv_symm_comp]
    exact ht
  obtain ⟨t, hte, hta, htp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanCartesianComparisonTriangle r e (a ≫ f) hbase hend haf
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianComparison_first_isInvertible r t (by rw [hte]; exact he)
      (by rw [hta]; exact haf) e htp
  let y := X.δ 1 (SSet.yonedaEquiv a)
  have hay : stdSimplex.δ (1 : Fin 2) ≫ a = SSet.yonedaEquiv.symm y := by
    rw [← SSet.yonedaEquiv.symm_apply_apply a, stdSimplex.δ_comp_yonedaEquiv_symm]
  have hk : stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ t) =
      SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y) := by
    have hδ : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
        stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [← Category.assoc, hδ, Category.assoc, hta, ← Category.assoc, hay,
      SSet.yonedaEquiv_symm_comp]
  have hkp : (stdSimplex.δ (2 : Fin 3) ≫ t) ≫ r =
      SSet.const (p.app (Opposite.op ⦋0⦌) y) := by
    have hδ : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        stdSimplex.σ (0 : Fin 2) = stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (1 : Fin 2) := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [Category.assoc, htp, ← hap, ← Category.assoc, hδ, Category.assoc,
      ← Category.assoc (stdSimplex.δ (1 : Fin 2)), hay,
      SSet.yonedaEquiv_symm_zero, SSet.const_comp, SSet.comp_const]
  obtain ⟨l, hlt, hlf, hli⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanVerticalInvertibleEdge_lift p r f hf hlift y
    (stdSimplex.δ (2 : Fin 3) ≫ t) hfirst hk hkp
  obtain ⟨u, hul, hua⟩ := horn₂₁.isPushout.exists_desc l a (hlt.trans hay.symm)
  have sq : CommSq u (horn 2 1).ι f t := by
    constructor
    apply horn₂₁.isPushout.hom_ext
    · rw [← Category.assoc, hul, hlf, ← Category.assoc, horn.ι_ι]
    · rw [← Category.assoc, hua, ← hta, ← Category.assoc, horn.ι_ι]
  have : HasLiftingProperty (horn 2 1).ι f :=
    InnerFibration.mem _ (innerHornInclusions.intro (1 : Fin 3) (by decide) (by decide))
  let s := sq.lift
  have hsl : stdSimplex.δ (2 : Fin 3) ≫ s = l := by
    rw [← horn.ι_ι_assoc 1 2 (by decide), sq.fac_left, hul]
  have hsa : stdSimplex.δ (0 : Fin 3) ≫ s = a := by
    rw [← horn.ι_ι_assoc 1 0 (by decide), sq.fac_left, hua]
  refine ⟨stdSimplex.δ (1 : Fin 3) ≫ s, ?_, ?_, ?_⟩
  · have hδ : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
        stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [← Category.assoc, hδ, Category.assoc, hsa, hat]
  · rw [Category.assoc, sq.fac_right, hte]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge s p
    · rw [hsl]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge p _ hli
    · rw [hsa]
      exact hac

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
