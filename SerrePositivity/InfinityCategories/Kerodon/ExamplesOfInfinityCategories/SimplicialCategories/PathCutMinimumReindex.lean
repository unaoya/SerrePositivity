module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutMinimum

/-!
概要：時間切断後の最小点を標準単体の反転への射にし、面・退化と可換にする。
方針：最小点の反単調性と任意の単調な添字写像への自然性を使う。
規約：添字写像の単射性を仮定せず、退化も同じ式で扱う。
使われ方：weighted prism の cone の係数を単体集合の射へ束ねる。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 切断後の最小点は、時間ラベルも引き戻した任意の添字変換と可換。 -/
lemma pathCutMinimum_reindex {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (n + 1) →o Fin 2) {j : Fin (m + 1)} (hj : t (α j) = 1)
    (P : Path (ULift.up 0 : ULift.{u} (Fin (m + 2))) (ULift.up j.succ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindex α P) = α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum (t.comp α) hj P) := by
  apply le_antisymm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_le
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_spec (t.comp α) hj P).1
    · exact ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum (t.comp α) hj P).succ,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_spec (t.comp α) hj P).2, rfl⟩
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_spec t hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindex α P)).2
    rcases hm with ⟨⟨k⟩, hk, he⟩
    induction k using Fin.cases with
    | zero =>
      have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) => a.down.val) he
      change 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindex α P)).val + 1 at he'
      omega
    | succ k =>
      have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) => a.down.val) he
      change (α k).val + 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindex α P)).val + 1 at he'
      have hv : α k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindex α P) := Fin.ext (by omega)
      have ht : (t.comp α) k = 1 := by
        change t (α k) = 1
        rw [hv]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_spec t hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindex α P)).1
      rw [← hv]
      exact α.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_le (t.comp α) hj P k ht hk)

/-- 最小点を反転すると、path の包含に対して単調な関手となる。 -/
noncomputable def pathCutMinimumReverseFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {a : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1) :
    Path (ULift.up a : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) ⥤
      ULift.{u} (Fin (n + 1)) where
  obj P := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj P).rev
  map f := homOfLE (Fin.rev_le_rev.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_antitone t hj f.1.1.1))

/-- 初点固定 cone の path を、同じ全パラメーターの標準単体の反転へ写す。 -/
noncomputable def pathCutMinimumMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {a : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1) :
    nerve (Path (ULift.up a : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      (Δ[n] : SSet.{u}).op :=
  nerveMap (pathCutMinimumReverseFunctor t hj) ≫
    (stdSimplex.isoNerve n).inv ≫ (stdSimplex.opIso ⦋n⦌).inv

/-- 標準単体の座標は、元の path の時刻一部分の最小点に一致する。 -/
lemma pathCutMinimumMap_apply {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {a : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1) {d : SimplexCategoryᵒᵖ}
    (P : (nerve (Path (ULift.up a : ULift.{u} (Fin (n + 2)))
      (ULift.up j.succ))).obj d) (k : Fin (d.unop.len + 1)) :
    (SSet.opObjEquiv ((pathCutMinimumMap t hj).app d P)).down.toOrderHom k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (P.obj k.rev) := by
  rcases d with ⟨⟨d⟩⟩
  change (SSet.opObjEquiv (stdSimplex.opObjEquiv.{u, u}.symm
    ((stdSimplex.isoNerve n).inv.app _
      ((nerveMap (pathCutMinimumReverseFunctor t hj)).app _ P)))) k = _
  rw [stdSimplex.opObjEquiv_opObjEquiv_symm_apply.{u, u}, stdSimplex.isoNerve_inv_app_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (P.obj k.rev)).rev.rev = _
  exact Fin.rev_rev _

/-- 時間切断後の係数射は、全ての面・退化の作用と厳密に可換。 -/
lemma pathCutMinimumMap_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (j : Fin (m + 1)) (hj : t (α.toOrderHom j) = 1) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫ pathCutMinimumMap t hj =
      pathCutMinimumMap (t.comp α.toOrderHom) hj ≫ SSet.opFunctor.map (stdSimplex.map α) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((pathCutMinimumMap t hj).app d
    (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j))).down.toOrderHom k =
      α.toOrderHom ((SSet.opObjEquiv
        ((pathCutMinimumMap (t.comp α.toOrderHom) hj).app d P)).down.toOrderHom k)
  rw [pathCutMinimumMap_apply, pathCutMinimumMap_apply]
  exact pathCutMinimum_reindex α.toOrderHom t hj (P.obj k.rev)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
