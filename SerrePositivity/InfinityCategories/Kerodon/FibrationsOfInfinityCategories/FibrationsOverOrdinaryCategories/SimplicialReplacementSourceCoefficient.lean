module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement

/-!
概要：simplicial replacement の係数単体を指定した始点の値へ揃える。
方針：底の始点の等式に沿って係数を輸送し、始点を保つ単調写像との自然性を示す。
規約：底の射列全体の等式ではなく、始点の対象の等式だけを入力する。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、§5.3.5（Tag 037H）、相対ホーンの係数の充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：simplicial replacement の単体の係数を指定対象の係数値で表示する。
方針：射列の始点と c の等式を係数関手で写して後合成する。
規約：s の次元と指定対象 c は任意。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、零番目以外の面の係数の標的を揃える。 -/
def simplicialReplacementSourceCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n)
    (c : C) (h : s.1.obj 0 = c) : (Δ[n] : SSet.{u}) ⟶ F.obj c :=
  s.2 ≫ F.map (eqToHom h)

/-- 概要：単体の等式は始点の表示を揃えた係数の等式を与える。
方針：等式を代入し、始点の等式の証明の一意性を使う。
規約：h と h' の証明の選択には依存しない。
使われ方：Kerodon §5.3.5（Tag 037H）、ホーン内の二つの面の係数の一致。 -/
lemma simplicialReplacementSourceCoefficient_congr {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n}
    (hst : s = t) (c : C) (h : s.1.obj 0 = c) (h' : t.1.obj 0 = c) :
    simplicialReplacementSourceCoefficient F s c h =
      simplicialReplacementSourceCoefficient F t c h' := by
  subst t
  rfl

/-- 概要：底の射列と指定始点での係数が同じなら simplicial replacement の単体は等しい。
方針：底の等式を代入し、係数の輸送の同型を後合成から消去する。
規約：底の射列全体の等式は別途指定する。
使われ方：Kerodon §5.3.5（Tag 037H）、係数の充填から元のホーン面の一致へ戻す判定。 -/
lemma simplicialReplacementSimplex_eq_of_sourceCoefficient
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n) (hb : s.1 = t.1)
    (c : C) (h : s.1.obj 0 = c) (h' : t.1.obj 0 = c)
    (he : simplicialReplacementSourceCoefficient F s c h =
      simplicialReplacementSourceCoefficient F t c h') : s = t := by
  rcases s with ⟨σ, u⟩
  rcases t with ⟨τ, v⟩
  change σ = τ at hb
  subst τ
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact (cancel_mono (F.map (eqToHom h))).1 he

/-- 概要：始点を保つ単調写像による制限は指定始点の係数の表示と可換。
方針：制限の式の始点の輸送を等式による輸送に置き換え、係数関手の合成則を使う。
規約：制限前後の始点の等式は任意の証明でよい。
使われ方：Kerodon §5.3.5（Tag 037H）、零番目以外の面の交わりから係数のホーンを作る。 -/
lemma simplicialReplacementSourceCoefficient_naturality
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n : SimplexCategory} (α : m ⟶ n) (hα : α.toOrderHom 0 = 0)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n.len) (c : C)
    (h : s.1.obj 0 = c)
    (h' : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F α s).1.obj 0 = c) :
    simplicialReplacementSourceCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F α s) c h' =
      stdSimplex.map α ≫ simplicialReplacementSourceCoefficient F s c h := by
  rcases s with ⟨σ, τ⟩
  change (stdSimplex.map α ≫ τ ≫ F.map (σ.map (homOfLE (Fin.zero_le _)))) ≫
      F.map (eqToHom h') = stdSimplex.map α ≫ τ ≫ F.map (eqToHom h)
  have hz : σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))) ≫ eqToHom h' = eqToHom h := by
    rw [show homOfLE (Fin.zero_le (α.toOrderHom 0)) = eqToHom hα.symm from
      Subsingleton.elim _ _, eqToHom_map, eqToHom_trans]
  simp only [Category.assoc]
  rw [← F.map_comp, hz]

/-- 概要：始点を保つ二つの制限で単体が一致すれば、指定始点の係数も制限上で一致する。
方針：制限後の始点の等式を作り、係数の自然性と単体の等式の輸送を合成する。
規約：二つの元の単体の次元は異なっていてもよい。
使われ方：Kerodon §5.3.5（Tag 037H）、ホーン面の交わりの係数の一致。 -/
lemma simplicialReplacementSourceCoefficient_overlap
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n r : SimplexCategory} (α : m ⟶ n) (β : m ⟶ r)
    (hα : α.toOrderHom 0 = 0) (hβ : β.toOrderHom 0 = 0)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n.len) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F r.len)
    (c : C) (hs : s.1.obj 0 = c) (ht : t.1.obj 0 = c)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F α s = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F β t) :
    stdSimplex.map α ≫ simplicialReplacementSourceCoefficient F s c hs =
      stdSimplex.map β ≫ simplicialReplacementSourceCoefficient F t c ht := by
  have hs' : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F α s).1.obj 0 = c :=
    (congrArg s.1.obj hα).trans hs
  have ht' : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F β t).1.obj 0 = c :=
    (congrArg t.1.obj hβ).trans ht
  calc
    _ = simplicialReplacementSourceCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F α s) c hs' :=
      (simplicialReplacementSourceCoefficient_naturality F α hα s c hs hs').symm
    _ = simplicialReplacementSourceCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F β t) c ht' :=
      simplicialReplacementSourceCoefficient_congr F he c hs' ht'
    _ = _ := simplicialReplacementSourceCoefficient_naturality F β hβ t c ht ht'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
