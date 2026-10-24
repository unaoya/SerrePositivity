module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialTriangleJoin

/-!
概要：三角形の最初の辺が cocartesian なら、その最初のホーンと境界の join を充填する。
方針：join のホーン同型で一つの高次元外側ホーンの持ち上げに移す。
規約：底の全図式と既定の部分図式を厳密に保つ。
使われ方：三角形に沿う cocartesian 性の消去の余錐の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した最初の辺の cocartesian 性で三角形と境界の相対 join を充填する。
方針：高次元の最初のホーンの充填を join の同型で戻す。
規約：q の inner fibration 性は不要。
使われ方：三角形の余錐を二つの辺の余錐から組み立てる最終ステップ。 -/
lemma triangleJoin_exists_lift {X Y : SSet.{u}} (q : X ⟶ Y) (n : ℕ)
    (T : (joinUnion (horn 2 0) (boundary n) : SSet.{u}) ⟶ X)
    (B : join (Δ[2] : SSet.{u}) Δ[n] ⟶ Y)
    (hw : T ≫ q = (joinUnion (horn 2 0) (boundary n)).ι ≫ B)
    (hc : IsCocartesianEdge q (SSet.yonedaEquiv
      ((stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        joinInl (Δ[2] : SSet.{u}) (boundary n : SSet.{u}) ≫
          joinUnionRight (horn 2 0) (boundary n) ≫ T))) :
    ∃ L : join (Δ[2] : SSet.{u}) Δ[n] ⟶ X,
      (joinUnion (horn 2 0) (boundary n)).ι ≫ L = T ∧ L ≫ q = B := by
  let σ := (SerrePositivity.InfinityCategories.initialTriangleHornJoinIso n).inv ≫ T
  let β := (SerrePositivity.InfinityCategories.initialTriangleJoinIso n).inv ≫ B
  have hσq : σ ≫ q = (horn (n + 3) 0).ι ≫ β := by
    dsimp only [σ, β]
    rw [Category.assoc, hw, ← Category.assoc,
      SerrePositivity.InfinityCategories.initialTriangleHornJoinIso_inv_ι, Category.assoc]
  let R := (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
    joinInl (Δ[2] : SSet.{u}) (boundary n : SSet.{u}) ≫
      joinUnionRight (horn 2 0) (boundary n)
  have he : σ.app (Opposite.op ⦋1⦌) (initialHornEdge (n + 1)) =
      SSet.yonedaEquiv (R ≫ T) := by
    have h := congrArg SSet.yonedaEquiv
      (show (R ≫ (SerrePositivity.InfinityCategories.initialTriangleHornJoinIso n).hom) ≫ σ = R ≫ T by
        dsimp only [σ]; rw [Category.assoc, Iso.hom_inv_id_assoc])
    rw [SSet.yonedaEquiv_comp] at h
    have hR : SSet.yonedaEquiv (R ≫ (SerrePositivity.InfinityCategories.initialTriangleHornJoinIso n).hom) =
        initialHornEdge (n + 1) := by
      simpa only [R, Category.assoc] using SerrePositivity.InfinityCategories.initialTriangleHornJoinIso_edge n
    rwa [hR] at h
  let sq : CommSq σ (horn (n + 3) 0).ι q β := ⟨hσq⟩
  have := hc (n + 1) σ β (by simpa only [R, Category.assoc] using he) sq
  refine ⟨(SerrePositivity.InfinityCategories.initialTriangleJoinIso n).hom ≫ sq.lift, ?_, ?_⟩
  · rw [← Category.assoc, ← SerrePositivity.InfinityCategories.initialTriangleHornJoinIso_hom_ι,
      Category.assoc, sq.fac_left]
    dsimp only [σ]
    rw [Iso.hom_inv_id_assoc]
  · rw [Category.assoc, sq.fac_right]
    exact (SerrePositivity.InfinityCategories.initialTriangleJoinIso n).hom_inv_id_assoc B

end SerrePositivity.InfinityCategories
