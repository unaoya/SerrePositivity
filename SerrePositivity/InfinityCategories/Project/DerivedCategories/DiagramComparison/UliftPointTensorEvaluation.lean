module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：点を固定した評価とULift・直積同型は同じ全パラメータの射を返す。
方針：二つの終対象射影の両逆則とΔ[0]の各成分の一意性を使う。
規約：IS-W2 B06の既存構成の単位・係数移送則。全単体を保持する。
使われ方：HA 1.2.4、指定Tot錐の制限の相対uncurryの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial

/-- 同じ点の評価とパラメータのULift・直積輸送の二つの合成は一致する。 -/
theorem uliftPointTensorEvaluation (K E Q S : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q) :
    let U := SSet.uliftFunctor.{v,u}
    let e := (uliftStdSimplexIso.{u,v} 0).inv ≫ U.map p
    let s := inv (fst (U.obj K) (Δ[0] : SSet.{max u v})) ≫
      (U.obj K ◁ e) ≫ (uliftTensorIso K E).inv ≫ U.map f
    s ▷ U.obj S =
      (U.obj K ◁ U.map (inv (snd (Δ[0] : SSet.{u}) S) ≫ (p ⊗ₘ 𝟙 S))) ≫
        (uliftTensorIso K (E ⊗ S)).inv ≫
          U.map ((α_ K E S).inv ≫ (f ▷ S)) ≫ (uliftTensorIso Q S).hom := by
  dsimp only
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, α⟩
  let b := (inv (fst ((SSet.uliftFunctor.{v,u}).obj K)
    (Δ[0] : SSet.{max u v}))).app n σ
  let c := (inv (snd (Δ[0] : SSet.{u}) S)).app n α.down
  let a := ((uliftStdSimplexIso.{u,v} 0).inv.app n b.2).down
  have hb := ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.inv_hom_id
    (fst ((SSet.uliftFunctor.{v,u}).obj K) (Δ[0] : SSet.{max u v}))) n) σ
  change b.1 = σ at hb
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.inv_hom_id
    (snd (Δ[0] : SSet.{u}) S)) n) α.down
  change c.2 = α.down at hc
  have ha : a = c.1 := by
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (_ : Fin 1) = (_ : Fin 1)
    exact Subsingleton.elim _ _
  change (ULift.up (f.app n (b.1.down, p.app n a)), α) =
    (ULift.up (f.app n (σ.down, p.app n c.1)), ULift.up c.2)
  rw [hb, ha, hc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
