module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.DoldKanGL
public import Mathlib.Algebra.Group.TransferInstance

/-!
# ĜL の連結成分と一般線形群

概要：π₀ で可逆な行列の単体的モノイドの連結成分を GL(π₀A) と同定する。
方針：各成分の辺を行列の辺にまとめ、単元行列の各成分の代表を選ぶ。
規約：KST 式 (2.2)。π₀ は Mathlib、成分の可逆性を各次数の可逆性に置き換えない。
使われ方：KST Lemma 2.13 に渡す群状性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped Simplicial

variable (A : SimplicialObject RingCat.{u}) (r : ℕ)

/--
概要：ĜL_r の台単体集合。
方針：単体的モノイドの忘却関手を合成する。
規約：KST 式 (2.2) の上左の単体集合。
使われ方：連結成分と分類空間。
-/
abbrev hatGLSpace : SSet.{u} := hatGLMonoidObject A r ⋙ forget MonCat

/--
概要：零次行列の成分写像は成分ごとの π₀ の商写像である。
方針：零次単体の成分写像を計算する。
規約：KST 式 (2.2) の行列の縦射。
使われ方：π₀ĜL の同定の各行列成分の計算。
-/
@[simp] theorem matrixToComponents_zero_entry
    (s : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌))) (i j : Fin r) :
    matrixToComponents A r 0 s i j = (π₀.mk (s i j) : π₀ (ringSpace A)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero (ringSpace A) (s i j)

/--
概要：ĜL_r の辺から各係数の辺を取り出す。
方針：一次行列を成分評価し、両端の等式も成分評価する。
規約：KST 式 (2.2) の部分単体集合としての包含。
使われ方：π₀ĜL から GL(π₀A) への写像の代表独立性。
-/
def hatGLCoefficientEdge {a b : hatGLSubmonoid A r 0}
    (e : (hatGLSpace A r).Edge a b) (i j : Fin r) :
    (ringSpace A).Edge (a.val i j) (b.val i j) :=
  .mk (e.edge.val i j)
    (congrArg (fun s : hatGLSubmonoid A r 0 => s.val i j) e.src_eq)
    (congrArg (fun s : hatGLSubmonoid A r 0 => s.val i j) e.tgt_eq)

/--
概要：各係数を結ぶ辺を ĜL_r の一本の辺にまとめる。
方針：辺の行列を作り、その成分が始点の成分と等しいことから可逆性を得る。
規約：行列自体の可逆性は仮定しない。KST 式 (2.2)。
使われ方：成分比較の単射性。
-/
def hatGLEdgeOfCoefficients (a b : hatGLSubmonoid A r 0)
    (e : ∀ i j : Fin r, (ringSpace A).Edge (a.val i j) (b.val i j)) :
    (hatGLSpace A r).Edge a b := by
  let E : Matrix (Fin r) (Fin r) (A.obj (op ⦋1⦌)) := fun i j => (e i j).edge
  have hs : (A.map (SimplexCategory.δ (1 : Fin 2)).op).hom.mapMatrix E = a.val := by
    apply Matrix.ext
    intro i j
    exact (e i j).src_eq
  have ht : (A.map (SimplexCategory.δ (0 : Fin 2)).op).hom.mapMatrix E = b.val := by
    apply Matrix.ext
    intro i j
    exact (e i j).tgt_eq
  have hE : E ∈ hatGLSubmonoid A r 1 := by
    change IsUnit (matrixToComponents A r 1 E)
    rw [← matrixToComponents_natural A r (SimplexCategory.δ (1 : Fin 2)), hs]
    exact a.property
  exact .mk ⟨E, hE⟩ (Subtype.ext hs) (Subtype.ext ht)

/--
概要：ĜL_r の零次単体の成分を一般線形群の元とする。
方針：単元性の証明から成分行列の二側逆を選ぶ。
規約：GL_r(π₀A) は行列環の単元群。KST 式 (2.2)。
使われ方：連結成分の比較写像。
-/
def hatGLVertexUnit (a : hatGLSubmonoid A r 0) :
    (Matrix (Fin r) (Fin r) (π₀ (ringSpace A)))ˣ := a.property.unit

/--
概要：同じ辺の両端の成分単元は等しい。
方針：各行列成分について辺が同じ π₀ を与えることを用いる。
規約：KST 式 (2.2) の連結成分の比較。
使われ方：商への降下。
-/
theorem hatGLVertexUnit_edge {a b : hatGLSubmonoid A r 0}
    (e : (hatGLSpace A r).Edge a b) : hatGLVertexUnit A r a = hatGLVertexUnit A r b := by
  apply Units.ext
  change (a.property.unit : Matrix (Fin r) (Fin r) (π₀ (ringSpace A))) = b.property.unit
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  apply Matrix.ext
  intro i j
  rw [matrixToComponents_zero_entry, matrixToComponents_zero_entry]
  exact π₀.sound (hatGLCoefficientEdge A r e i j)

/--
概要：π₀ĜL_r から GL_r(π₀A) への標準写像。
方針：零次単体の成分単元を辺の関係で商へ降ろす。
規約：KST 式 (2.2) の成分の同定に用いる写像。
使われ方：群状性と分類空間の π₁ の計算。
-/
def hatGLClassMap : π₀ (hatGLSpace A r) → (Matrix (Fin r) (Fin r) (π₀ (ringSpace A)))ˣ :=
  π₀.lift (hatGLVertexUnit A r) (fun _ _ e => hatGLVertexUnit_edge A r e)

/--
概要：成分単元が等しい零次単体は ĜL_r で同じ連結成分にある。
方針：成分ごとの π₀ の等式を一本の辺へ直し、行列の辺にまとめる。
規約：KST 式 (2.2)。加法的辺の連結を使うので Kan 性の仮定は不要。
使われ方：π₀ĜL_r の比較写像の単射性。
-/
theorem hatGLClassMap_injective : Function.Injective (hatGLClassMap A r) := by
  intro x y h
  induction x using π₀.rec with | mk a => ?_
  induction y using π₀.rec with | mk b => ?_
  have hm : matrixToComponents A r 0 a.val = matrixToComponents A r 0 b.val := by
    have hv := congrArg Units.val h
    change (a.property.unit : Matrix (Fin r) (Fin r) (π₀ (ringSpace A))) = b.property.unit at hv
    simpa only [IsUnit.unit_spec] using hv
  have he : ∀ i j : Fin r, Nonempty ((ringSpace A).Edge (a.val i j) (b.val i j)) := by
    intro i j
    apply SimplicialRing.nonempty_edge_of_mk_eq A
    simpa only [matrixToComponents_zero_entry] using congrArg (fun M => M i j) hm
  exact π₀.sound (hatGLEdgeOfCoefficients A r a b (fun i j => Classical.choice (he i j)))

/--
概要：全ての GL_r(π₀A) の元は ĜL_r の連結成分から来る。
方針：各行列成分の零単体の代表を選ぶ。
規約：持ち上げた行列の strict な可逆性は不要。KST 式 (2.2)。
使われ方：π₀ĜL_r の比較写像の全射性。
-/
theorem hatGLClassMap_surjective : Function.Surjective (hatGLClassMap A r) := by
  intro g
  have hs : ∀ i j : Fin r, ∃ a : A.obj (op ⦋0⦌), (π₀.mk a : π₀ (ringSpace A)) = g.val i j :=
    fun i j => π₀.mk_surjective (g.val i j)
  choose a ha using hs
  have hm : matrixToComponents A r 0 a = g.val := by
    apply Matrix.ext
    intro i j
    rw [matrixToComponents_zero_entry]
    exact ha i j
  have hu : a ∈ hatGLSubmonoid A r 0 := by
    change IsUnit (matrixToComponents A r 0 a)
    rw [hm]
    exact g.isUnit
  refine ⟨π₀.mk (⟨a, hu⟩ : hatGLSubmonoid A r 0), ?_⟩
  apply Units.ext
  change (hu.unit : Matrix (Fin r) (Fin r) (π₀ (ringSpace A))) = g.val
  rw [IsUnit.unit_spec]
  exact hm

/--
概要：π₀ĜL_r(A) と GL_r(π₀A) を全単射で同定する。
方針：成分行列の写像の単射性と全射性を合わせる。
規約：KST 式 (2.2)。群構造と乗法の整合は別途述べる。
使われ方：群状性と Segal 1974 Proposition 1.5 の適用。
-/
def hatGLComponentsEquiv : π₀ (hatGLSpace A r) ≃
    (Matrix (Fin r) (Fin r) (π₀ (ringSpace A)))ˣ :=
  Equiv.ofBijective (hatGLClassMap A r) ⟨hatGLClassMap_injective A r, hatGLClassMap_surjective A r⟩

/--
概要：ĜL_r の連結成分に一般線形群から群構造を入れる。
方針：成分写像の全単射を通じて群の全ての演算を輸送する。
規約：KST §2.2 の群状性。各次数に群構造は導入しない。
使われ方：BĜL_r のホモトピー群の比較。
-/
instance hatGLComponentsGroup : Group (π₀ (hatGLSpace A r)) :=
  (hatGLComponentsEquiv A r).group

/--
概要：π₀ĜL_r と GL_r(π₀A) の同定は群の乗法を保つ。
方針：全単射によって輸送した群の標準乗法同値を用いる。
規約：KST 式 (2.2) の群状性の同定。
使われ方：分類空間の π₁ の群としての計算。
-/
def hatGLComponentsMulEquiv : π₀ (hatGLSpace A r) ≃*
    (Matrix (Fin r) (Fin r) (π₀ (ringSpace A)))ˣ :=
  (hatGLComponentsEquiv A r).mulEquiv

/--
概要：零次単体の積の成分単元は成分単元の積である。
方針：成分への環準同型の積の保存を使う。
規約：KST 式 (2.2) の行列乗法の順序を保つ。
使われ方：輸送した群構造が実際の単体的モノイドから誘導されることの確認。
-/
theorem hatGLVertexUnit_mul (a b : hatGLSubmonoid A r 0) :
    hatGLVertexUnit A r (a * b) = hatGLVertexUnit A r a * hatGLVertexUnit A r b := by
  apply Units.ext
  simp only [hatGLVertexUnit, IsUnit.unit_spec, Units.val_mul]
  exact (matrixToComponents A r 0).map_mul a.val b.val

/--
概要：単体的モノイドの零次の積は π₀ の群の積に降りる。
方針：成分単元への乗法同値の単射性を使う。
規約：任意の全単射による無関係な群構造ではないことを明記する。KST 式 (2.2)。
使われ方：Segal 1974 Proposition 1.5 の群状性。
-/
theorem hatGL_mk_mul (a b : hatGLSubmonoid A r 0) :
    (π₀.mk (a * b) : π₀ (hatGLSpace A r)) = π₀.mk a * π₀.mk b := by
  apply (hatGLComponentsMulEquiv A r).injective
  rw [map_mul]
  exact hatGLVertexUnit_mul A r a b

/--
概要：単体的モノイドの単位は π₀ の群の単位に降りる。
方針：成分単元への同値で単位元の値を計算する。
規約：KST 式 (2.2) の単位の整合。
使われ方：ĜL_r が群状単体的モノイドであること。
-/
theorem hatGL_mk_one : (π₀.mk (1 : hatGLSubmonoid A r 0) : π₀ (hatGLSpace A r)) = 1 := by
  apply (hatGLComponentsMulEquiv A r).injective
  rw [map_one]
  apply Units.ext
  simp only [hatGLComponentsMulEquiv, Equiv.mulEquiv_apply, hatGLComponentsEquiv,
    Equiv.ofBijective_apply, hatGLClassMap, π₀.lift_mk, hatGLVertexUnit,
    IsUnit.unit_spec, Units.val_one]
  exact (matrixToComponents A r 0).map_one

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (2.2)" (partial := component) "仮定：単位つき単体環の有限階数行列を用いる（Lean が強い：原典は非単位的環も含む）。結論：指定成分に制限した行列モノイドとその成分群。任意の非単位的単体環の安定化した ĜL までの同定は別（Lean が弱い）。"] _root_.SerrePositivity.KST.Comparison.hatGLComponentsMulEquiv
