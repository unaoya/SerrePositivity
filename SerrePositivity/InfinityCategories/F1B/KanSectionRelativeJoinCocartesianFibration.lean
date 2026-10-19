module

public import SerrePositivity.InfinityCategories.F1.IntervalCocartesianCriterion
public import SerrePositivity.InfinityCategories.F1B.KanSectionRelativeJoinCrossingCocartesian
public import SerrePositivity.InfinityCategories.F1.RelativeJoinEndpointFibers
public import SerrePositivity.InfinityCategories.F1.JoinQuasicategory

/-!
概要：関手の相対 join の区間への射影は cocartesian fibration。
方針：零 fiber を左因子で表示し、標準 prism の垂直辺で区間の標準辺を持ち上げる。
規約：両因子は quasicategory、右因子の構造射は恒等射。
使われ方：Kerodon Proposition 5.2.3.15、Theorem 5.2.4.1 の比較の始域。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection

/-- 概要：相対 join の時刻零の頂点は左因子の頂点から来る。
方針：頂点を零 fiber に持ち上げ、左因子との標準同型の逆で戻す。
規約：二つの構造射は任意。
使われ方：Kerodon Proposition 5.2.3.15、標準 prism の始点の指定。 -/
lemma relativeJoin_vertex_inl_of_projection_zero {X Y S : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (x : (relativeJoin f g) _⦋0⦌)
    (hx : (relativeJoinProjection f g).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    ∃ y : X _⦋0⦌, (relativeJoinInl f g).app (Opposite.op ⦋0⦌) y = x := by
  let z : (vertexFiber (relativeJoinProjection f g)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) _⦋0⦌ :=
    ⟨x, by simpa only [PinchedHom.constant_zero] using hx⟩
  let y := (relativeJoinZeroFiberIso f g).inv.app (Opposite.op ⦋0⦌) z
  have hi := ConcreteCategory.congr_hom
    (NatTrans.congr_app (relativeJoinZeroFiberIso f g).inv_hom_id (Opposite.op ⦋0⦌)) z
  change (relativeJoinZeroFiberIso f g).hom.app (Opposite.op ⦋0⦌) y = z at hi
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) y)
    (relativeJoinZeroFiberIso_hom_ι f g)
  refine ⟨y, he.symm.trans ?_⟩
  exact congrArg (fun v ↦ (vertexFiberι (relativeJoinProjection f g)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v) hi

/-- 概要：二つの quasicategory の間の関手の相対 join は区間上の cocartesian fibration。
方針：零 fiber の各頂点を標準 prism の垂直辺で持ち上げ、区間の判定補題を適用する。
規約：係数の極限・余極限や分類定理は使わない。
使われ方：Kerodon Proposition 5.2.3.15、Theorem 5.2.4.1 の写像円柱比較。 -/
instance relativeJoinProjection_cocartesianFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    CocartesianFibration (relativeJoinProjection f (𝟙 Y)) := by
  apply cocartesianFibration_interval_of_lift
  intro x hx
  obtain ⟨y, hy⟩ := relativeJoin_vertex_inl_of_projection_zero f (𝟙 Y) x hx
  let k : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ X := lift (𝟙 Δ[1]) (SSet.const y)
  let l := k ≫ relativeJoinPrism f
  have hk : stdSimplex.δ (1 : Fin 2) ≫ k = SSet.yonedaEquiv.symm y ≫ prismEndpoint 0 X := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [k, prismEndpoint, Category.assoc, lift_fst, Category.comp_id,
        SSet.comp_const, stdSimplex.δ_one_eq_const]
    · simp only [k, prismEndpoint, Category.assoc, lift_snd, Category.comp_id,
        SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  refine ⟨l, ?_, ?_, ?_⟩
  · change (stdSimplex.δ 1 ≫ k) ≫ relativeJoinPrism f = SSet.yonedaEquiv.symm x
    rw [hk, Category.assoc, relativeJoinPrism_zero, SSet.yonedaEquiv_symm_comp, hy]
  · change k ≫ relativeJoinPrism f ≫ relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1]
    rw [relativeJoinPrism_projection]
    exact lift_fst _ _
  · change IsCocartesianEdge (relativeJoinProjection f (𝟙 Y))
      (prismVerticalSimplex (relativeJoinPrism f) y)
    exact relativeJoinPrism_vertical_isCocartesian f y

end SerrePositivity.InfinityCategories.KanSection
