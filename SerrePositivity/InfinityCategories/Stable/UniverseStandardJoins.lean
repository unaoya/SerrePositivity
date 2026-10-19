module
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns

/-! # 標準単体の join 同型の宇宙整合性

概要：二つの標準単体の join と和次数の標準単体との同型は宇宙比較と可換。
方針：左右の増大単体の順序写像が同じであることから連結写像を比較する。
規約：空の増大単体を含む。使われ方：span/cospan の三角形の宇宙比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

/-- 空区間を含む標準増大単体の順序写像は宇宙を上げても同じ。 -/
lemma uliftStandardAug_order (n r : ℕ) (x : Join.augObj (Δ[n] : SSet.{u}) r) :
    Join.stdAugEquiv n r (Join.augHom (uliftStdSimplexIso.{u, v} n).hom r
      (uliftJoinAugUp Δ[n] r x)) = Join.stdAugEquiv n r x := by
  cases r with
  | zero => ext a; exact Fin.elim0 a
  | succ r => rfl

/-- 二つの標準単体の join を持ち上げる実形状同型。 -/
def uliftStandardJoinIso (i j : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (join (Δ[i] : SSet.{u}) Δ[j]) ≅
      join (Δ[i] : SSet.{max u v}) Δ[j] :=
  uliftJoinIso Δ[i] Δ[j] ≪≫ joinIso (uliftStdSimplexIso i) (uliftStdSimplexIso j)

/-- 標準単体の join 同型と宇宙比較の可換性。 -/
lemma uliftStandardJoinIso_std (i j : ℕ) :
    (uliftStandardJoinIso.{u, v} i j).hom ≫ (joinStdSimplexIso i j).hom =
      (SSet.uliftFunctor.{v, u}).map (joinStdSimplexIso i j).hom ≫
        (uliftStdSimplexIso.{u, v} (i + j + 1)).hom := by
  ext d s
  change Join.stdSimplexTargetEquiv i j d.unop.len
    (Join.stdEncode i j d.unop.len
      ((uliftStandardJoinIso.{u, v} i j).hom.app d s)) =
        Join.stdSimplexTargetEquiv i j d.unop.len (Join.stdEncode i j d.unop.len s.down)
  apply congrArg (Join.stdSimplexTargetEquiv i j d.unop.len)
  change Join.concat s.down.1.val _
    (Join.stdAugEquiv i _ (Join.augHom (uliftStdSimplexIso i).hom _
      (uliftJoinAugUp Δ[i] _ s.down.2.1)))
    (Join.stdAugEquiv j _ (Join.augHom (uliftStdSimplexIso j).hom _
      (uliftJoinAugUp Δ[j] _ s.down.2.2))) = _
  rw [uliftStandardAug_order, uliftStandardAug_order]
  rfl

/-- 標準単体の join の逆同型も宇宙比較と可換。 -/
lemma uliftStandardJoinIso_std_inv (i j : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (joinStdSimplexIso i j).inv ≫
        (uliftStandardJoinIso.{u, v} i j).hom =
      (uliftStdSimplexIso.{u, v} (i + j + 1)).hom ≫ (joinStdSimplexIso i j).inv := by
  apply (cancel_mono (joinStdSimplexIso i j).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [uliftStandardJoinIso_std, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, (SSet.uliftFunctor.{v, u}).map_id, Category.id_comp]

end SerrePositivity.InfinityCategories
