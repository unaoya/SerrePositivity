module

public import SerrePositivity.KST.Comparison.MonoidComponentsFunctor

/-!
# 定数モノイドへの射の成分への降下

概要：定数単体的モノイドへの自然変換を、実際の成分モノイドの準同型へ降ろす。
方針：二つの端点での自然性から辺上での一致を示し、π₀ の商の普遍性を使う。
規約：KST 式 (2.3)、Lemma 2.13 の成分関手の随伴の補助。
使われ方：安定成分の余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial
namespace SimplicialMonoid

/--
概要：定数モノイドへの自然変換の零次写像は辺の両端で一致する。
方針：一次単体の二つの面の自然性を使う。
規約：元の単体的モノイドに群状性は不要。
使われ方：連結成分の商への降下の条件。
-/
theorem constantMap_edge {M : SimplicialObject MonCat.{u}} (N : MonCat.{u})
    (f : M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj N)
    {a b : (monoidSpace M).obj (op ⦋0⦌)} (e : (monoidSpace M).Edge a b) :
    (f.app (op ⦋0⦌)).hom a = (f.app (op ⦋0⦌)).hom b := by
  have hf (i : Fin 2) : (f.app (op ⦋0⦌)).hom
      ((M.map (SimplexCategory.δ i).op).hom e.edge) = (f.app (op ⦋1⦌)).hom e.edge := by
    have h := congrArg (fun t => t.hom e.edge) (f.naturality (SimplexCategory.δ i).op)
    exact h
  calc
    _ = (f.app (op ⦋0⦌)).hom ((monoidSpace M).δ 1 e.edge) :=
      congrArg (f.app (op ⦋0⦌)).hom e.src_eq.symm
    _ = (f.app (op ⦋1⦌)).hom e.edge := hf 1
    _ = (f.app (op ⦋0⦌)).hom ((monoidSpace M).δ 0 e.edge) := (hf 0).symm
    _ = _ := congrArg (f.app (op ⦋0⦌)).hom e.tgt_eq

/--
概要：定数モノイドへの射は、連結成分のモノイド射へ降りる。
方針：辺の両端の一致で π₀.lift を使い、積と単位は零単体の代表で確認する。
規約：元の射の零次写像と整合する具体的な準同型。
使われ方：定数関手との Hom 同値。
-/
def componentsDesc {M : SimplicialObject MonCat.{u}} (N : MonCat.{u})
    (f : M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj N) : componentsObject M →* N where
  toFun := π₀.lift (f.app (op ⦋0⦌)).hom (fun _ _ e => constantMap_edge N f e)
  map_one' := map_one (f.app (op ⦋0⦌)).hom
  map_mul' a b := by
    let : Monoid ((monoidSpace M).obj (op ⦋0⦌)) := inferInstanceAs (Monoid (M.obj (op ⦋0⦌)))
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    exact map_mul (f.app (op ⦋0⦌)).hom a b

/--
概要：成分への各次数の射は零次では元の商写像である。
方針：零単体への最初の頂点の射を恒等射と同定する。
規約：成分の型は Mathlib の実際の π₀。
使われ方：成分の降下の逆写像の計算。
-/
theorem simplexToComponents_zero (M : SimplicialObject MonCat.{u})
    (a : M.obj (op ⦋0⦌)) : simplexToComponents M 0 a = π₀.mk a := by
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  unfold simplexToComponents
  rw [h, op_id, M.map_id]
  rfl

end SimplicialMonoid
end SerrePositivity.KST.Comparison
