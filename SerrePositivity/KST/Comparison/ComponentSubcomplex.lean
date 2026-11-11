module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 連結成分の集合で指定した部分単体集合

概要：π₀ の一部を選ぶと、その成分全体からなる部分単体集合を得る。
方針：単体の連結成分による逆像を取り、辺の列による商を比較する。
規約：高次 π_n と Kan 性は不要。π₀ は Mathlib の定義を使う。
使われ方：KST 式 (2.2) の単元成分の逆像と π₀ĜL の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped _root_.Simplicial

/--
概要：指定した連結成分の全単体からなる部分単体集合。
方針：`simplexClass` の逆像を各次数で取り、単体作用の不変性を使う。
規約：P は π₀ の任意の性質。KST 式 (2.2) では可逆性を指定する。
使われ方：ĜL と連結成分の群との比較。
-/
def componentSubcomplex (X : SSet.{u}) (P : π₀ X → Prop) : X.Subcomplex where
  obj n := {s | P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X s)}
  map f s hs := by
    change P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (X.map f s))
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map X f.unop s).symm ▸ hs

/--
概要：指定した成分に属する頂点を部分単体集合へ持ち上げる。
方針：零次での成分写像の計算を使う。
規約：KST 式 (2.2) の零次数の逆像。
使われ方：π₀ の商の代表を部分単体集合で選ぶ。
-/
def componentVertex (X : SSet.{u}) (P : π₀ X → Prop) (a : X _⦋0⦌) (ha : P (π₀.mk a)) :
    (componentSubcomplex X P : SSet) _⦋0⦌ :=
  ⟨a, by
    change P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X a)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero] using ha⟩

/--
概要：成分を指定した部分単体集合へ、両端を含む辺を持ち上げる。
方針：辺の成分は始点の成分に等しいことを使う。
規約：始点の条件だけで辺全体が選ばれる。KST 式 (2.2)。
使われ方：部分単体集合の π₀ の単射性。
-/
def componentEdge (X : SSet.{u}) (P : π₀ X → Prop) {a b : X _⦋0⦌}
    (ha : P (π₀.mk a)) (hb : P (π₀.mk b)) (e : X.Edge a b) :
    (componentSubcomplex X P : SSet).Edge (componentVertex X P a ha) (componentVertex X P b hb) :=
  .mk ⟨e.edge, by
    have h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X e.edge = π₀.mk a := by
      change π₀.mk (X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op e.edge) = _
      rw [← SimplexCategory.δ_one_eq_const]
      exact congrArg π₀.mk e.src_eq
    change P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X e.edge)
    rw [h]
    exact ha⟩
    (Subtype.ext e.src_eq) (Subtype.ext e.tgt_eq)

/--
概要：元の単体集合で同じ成分の二頂点は、選んだ部分単体集合でも同じ成分にある。
方針：辺による同値閉包に帰納し、中間点の成分条件を輸送する。
規約：部分単体集合は成分全体を含む。KST 式 (2.2) の π₀ の計算。
使われ方：包含による連結成分の単射性。
-/
theorem componentVertex_sound (X : SSet.{u}) (P : π₀ X → Prop) {a b : X _⦋0⦌}
    (h : π₀.mk a = π₀.mk b) (ha : P (π₀.mk a)) (hb : P (π₀.mk b)) :
    π₀.mk (componentVertex X P a ha) = π₀.mk (componentVertex X P b hb) := by
  have hr := (π₀.mk_eq_mk_iff a b).mp h
  clear h
  induction hr with
  | rel a b h =>
    obtain ⟨e⟩ := h
    exact π₀.sound (componentEdge X P ha hb e)
  | refl a => rfl
  | symm a b h ih => exact (ih hb ha).symm
  | trans a b c h₁ h₂ ih₁ ih₂ =>
    have hm : P (π₀.mk b) := ((π₀.mk_eq_mk_iff a b).mpr h₁) ▸ ha
    exact (ih₁ ha hm).trans (ih₂ hm hb)

/--
概要：部分単体集合の連結成分を選ばれた元の連結成分へ送る。
方針：頂点の包含を商へ降ろす。
規約：値には選択条件 P の証明も保持する。KST 式 (2.2)。
使われ方：連結成分の標準全単射。
-/
def componentClassMap (X : SSet.{u}) (P : π₀ X → Prop) :
    π₀ (componentSubcomplex X P : SSet) → {c : π₀ X // P c} :=
  π₀.lift (fun a => ⟨π₀.mk a.val, by
    have ha : P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X a.val) := a.property
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero] using ha⟩)
    (fun _ _ e => Subtype.ext (π₀.sound (e.map (componentSubcomplex X P).ι)))

/--
概要：選んだ部分単体集合の π₀ は選ばれた成分の集合と全単射である。
方針：全射性は頂点代表の選択、単射性は辺の同値閉包の持ち上げから従う。
規約：選択公理は全単射の逆写像の選択にのみ使う。KST 式 (2.2) の成分比較。
使われ方：π₀ĜL_n と GL_n(π₀A) の同定。
-/
noncomputable def componentClassEquiv (X : SSet.{u}) (P : π₀ X → Prop) :
    π₀ (componentSubcomplex X P : SSet) ≃ {c : π₀ X // P c} :=
  Equiv.ofBijective (componentClassMap X P) ⟨by
    intro x y h
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    have hx : P (π₀.mk x.val) := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero] using (show P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X x.val) from x.property)
    have hy : P (π₀.mk y.val) := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero] using (show P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X y.val) from y.property)
    exact componentVertex_sound X P (congrArg Subtype.val h) hx hy, by
    rintro ⟨c, hc⟩
    obtain ⟨a, rfl⟩ := π₀.mk_surjective c
    exact ⟨π₀.mk (componentVertex X P a hc), rfl⟩⟩

end SerrePositivity.KST.Comparison
