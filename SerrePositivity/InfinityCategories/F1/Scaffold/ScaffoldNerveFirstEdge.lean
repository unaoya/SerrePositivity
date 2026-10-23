module

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldNerveBridge

/-!
概要：有限鎖の錐への比較の区間部分を最初の辺として同定する。
方針：零頂点の標準単体表示と join の自然性を使う。
規約：最初の辺は頂点 0、1 を順に取る通常の関手の nerve。
使われ方：Kerodon Theorem 5.3.5.7、有限鎖の円柱部分の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：有限鎖の最初の二頂点への包含関手。
方針：二頂点の値をそのまま全有限鎖へ含める単調写像を使う。
規約：0 を 0、1 を 1 に写す。
使われ方：Kerodon Theorem 5.3.5.7、最初の辺の simplicial replacement。 -/
def scaffoldFiniteFirstEdge (n : ℕ) :
    ULift.{u} (Fin 2) ⥤ ULift.{u} (Fin (n + 2)) :=
  (show ULift.{u} (Fin 2) →o ULift.{u} (Fin (n + 2)) from
    { toFun := fun i ↦ ULift.up ⟨i.down.val, by have := i.down.isLt; omega⟩
      monotone' := fun _ _ h ↦ h }).monotone.functor

/-- 概要：有限鎖の最初の頂点の標準単体表示は零への定値写像。
方針：Yoneda 同値で零単体を比較する。
規約：nerve の標準単体同型の逆向きを使う。
使われ方：Kerodon Theorem 5.3.5.7、join の自然性の適用。 -/
lemma scaffoldFiniteNervePoint_isoNerve (n : ℕ) :
    nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _) ≫
      (stdSimplex.isoNerve n).inv =
        stdSimplex.map (SimplexCategory.mkHom (OrderHom.const _ (0 : Fin (n + 1)))) := by
  apply SSet.yonedaEquiv.injective
  ext i
  rfl

/-- 概要：零定値写像に始点を加えた辺は有限鎖の最初の辺に対応する。
方針：単体ごとの各頂点の値を比較する。
規約：左の始域は標準区間。
使われ方：Kerodon Theorem 5.3.5.7、区間と有限鎖の表示の整合性。 -/
lemma scaffoldFiniteFirstEdge_isoNerve (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom
        (prependOrderHom (OrderHom.const _ (0 : Fin (n + 1))))) ≫
      (stdSimplex.isoNerve.{u} (n + 1)).hom =
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n) := by
  ext d s i
  change (Δ[1] _⦋d.unop.len⦌ : Type u) at s
  change (prependOrderHom (OrderHom.const _ (0 : Fin (n + 1))) (s i)).val = (s i).val
  have h := (s i).isLt
  rcases he : (s i).val with _ | k
  · have hs : s i = 0 := Fin.ext he
    rw [hs, prependOrderHom_zero]
    rfl
  · have hk : k = 0 := by omega
    subst k
    have hs : s i = (0 : Fin 1).succ := Fin.ext he
    rw [hs, prependOrderHom_succ]
    rfl

/-- 概要：最初の辺と尾部の比較は区間上で最初の辺の nerve になる。
方針：pushout の計算則の後、零頂点の表示と join の自然性を使う。
規約：区間から二頂点の nerve への標準同型を前置する。
使われ方：Kerodon Theorem 5.3.5.7、円柱から全体の replacement への射の同定。 -/
lemma scaffoldFiniteNerveBridge_inl (n : ℕ) :
    pushout.inl (stdSimplex.δ (0 : Fin 2))
        (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ≫
      scaffoldFiniteNerveBridge n =
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n) := by
  rw [scaffoldFiniteNerveBridge, scaffoldNerveConeBridge, ← Category.assoc,
    pushout.inl_desc]
  change ((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (nervePoint (ULift.up 0))) ≫
    (joinMap (𝟙 Δ[0]) (stdSimplex.isoNerve n).inv ≫
      (pointJoinStdSimplexIso n).hom ≫ (stdSimplex.isoNerve (n + 1)).hom) = _
  rw [Category.assoc, ← Category.assoc (joinMap _ _), ← joinMap_comp,
    Category.id_comp, scaffoldFiniteNervePoint_isoNerve,
    ← Category.assoc (joinMap _ _), joinStdSimplexIso_point_naturality]
  change (joinStdSimplexIso 0 0).inv ≫ ((joinStdSimplexIso 0 0).hom ≫
    stdSimplex.map (SimplexCategory.mkHom
      (prependOrderHom (OrderHom.const _ (0 : Fin (n + 1)))))) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, scaffoldFiniteFirstEdge_isoNerve]

end SerrePositivity.InfinityCategories
