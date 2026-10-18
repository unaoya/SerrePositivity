module
public import SerrePositivity.KST.ProExcision.SetActionBar
public import SerrePositivity.KST.ProExcision.ActionNerveWord

/-!
# 作用 bar の語を固定した係数の包含

概要：E_X G の各次数で、G の語を固定して係数 X を入れる。
方針：作用圏の始点と射影の語の全単射を使う。
規約：KST Lemma A.4 の線形持ち上げの準備。
使われ方：自由整数加群の線形写像を、語ごとに bar へ入れる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
variable {G : SimplicialObject MonCat.{u}} {X : SSet.{u}}

/-- 概要：作用 bar から作用するモノイドの分類空間への射影。
方針：各単体の作用圏の射列をラベルの語へ送る。
規約：KST Lemma A.4。使われ方：語を固定した係数包含の自然性。 -/
def setActionBarProjection (A : SimplicialSetAction G X) : setActionBar A ⟶ monoidBar G where
  app n := by
    letI := A.actionStructure n
    exact ↾fun p ↦ p ⋙ actionCategoryProjection (G := G.obj n) (X := X.obj n)
  naturality n m f := by rfl

/-- 概要：語を固定した係数の基底単体の包含。
方針：始点と語の全単射の逆を使う。
規約：KST Lemma A.4。使われ方：区間写像の線形な持ち上げ。 -/
def setActionBarFiberSection (A : SimplicialSetAction G X) (n : SimplexCategoryᵒᵖ)
    (w : (monoidBar G).obj n) : X.obj n → (setActionBar A).obj n :=
  letI := A.actionStructure n
  fun x ↦ actionNerveWordSection (G := G.obj n) (X := X.obj n) x w

/-- 概要：語を固定した包含は射影で指定した語に戻る。
方針：作用圏の語の座標の右逆を使う。
規約：KST Lemma A.4。使われ方：単体射での語の移送。 -/
@[simp] lemma setActionBarFiberSection_projection (A : SimplicialSetAction G X)
    (n : SimplexCategoryᵒᵖ) (w : (monoidBar G).obj n) (x : X.obj n) :
    (setActionBarProjection A).app n (setActionBarFiberSection A n w x) = w := by
  letI := A.actionStructure n
  exact actionNerveWordSection_projection (G := G.obj n) (X := X.obj n) x w

/-- 概要：語を固定した包含の始点は指定した係数。
方針：作用圏の語の座標の右逆を使う。
規約：KST Lemma A.4。使われ方：区間写像の両端条件。 -/
@[simp] lemma setActionBarFiberSection_source (A : SimplicialSetAction G X)
    (n : SimplexCategoryᵒᵖ) (w : (monoidBar G).obj n) (x : X.obj n) :
    ((setActionBarFiberSection A n w x).obj 0).val = x := by
  letI := A.actionStructure n
  exact actionNerveWordSection_source (G := G.obj n) (X := X.obj n) x w

/-- 概要：単体射の最初の頂点までの prefix のラベル。
方針：分類空間の語の始点からその頂点までの合成射を評価する。
規約：KST Lemma A.4 の作用 bar の単体射。使われ方：係数の始点の移送。 -/
def barWordFacePrefix {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (w : (monoidBar G).obj n) :
    G.obj n :=
  w.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))

/-- 概要：単体射は固定した語の係数を prefix の作用で移す。
方針：作用圏の始点から像の最初の頂点への射の条件と、語の射影の自然性を使う。
規約：KST Lemma A.4、任意の面と退化を同時に扱う。
使われ方：同変な線形区間写像の bar への持ち上げの自然性。 -/
theorem setActionBarFiberSection_naturality (A : SimplicialSetAction G X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (w : (monoidBar G).obj n) (x : X.obj n) :
    (setActionBar A).map f (setActionBarFiberSection A n w x) =
      setActionBarFiberSection A m ((monoidBar G).map f w)
        (X.map f (A.action n (barWordFacePrefix f w) x)) := by
  letI := A.actionStructure n
  letI := A.actionStructure m
  let p := setActionBarFiberSection A n w x
  have hs : (p.obj 0).val = x := setActionBarFiberSection_source A n w x
  have hw : p ⋙ actionCategoryProjection (G := G.obj n) (X := X.obj n) = w :=
    actionNerveWordSection_projection (G := G.obj n) (X := X.obj n) x w
  let a := homOfLE (Fin.zero_le (f.unop.toOrderHom 0))
  have hl : (p.map a).val = w.map a := congrArg (fun q ↦ q.map a) hw
  have hp := (p.map a).property
  change A.action n (p.map a).val (p.obj 0).val = (p.obj (f.unop.toOrderHom 0)).val at hp
  rw [hl, hs] at hp
  apply actionNerveWordCoordinates_injective (G := G.obj m) (X := X.obj m) m.unop.len
  apply Prod.ext
  · change X.map f (p.obj (f.unop.toOrderHom 0)).val =
      ((setActionBarFiberSection A m ((monoidBar G).map f w)
        (X.map f (A.action n (barWordFacePrefix f w) x))).obj 0).val
    rw [setActionBarFiberSection_source]
    exact congrArg (X.map f) hp.symm
  · change (setActionBarProjection A).app m ((setActionBar A).map f p) =
      (setActionBarProjection A).app m
        (setActionBarFiberSection A m ((monoidBar G).map f w)
          (X.map f (A.action n (barWordFacePrefix f w) x)))
    rw [setActionBarFiberSection_projection]
    have hn := congrArg (fun q ↦ q p) ((setActionBarProjection A).naturality f)
    change (setActionBarProjection A).app m ((setActionBar A).map f p) =
      (monoidBar G).map f ((setActionBarProjection A).app n p) at hn
    have hpw : (setActionBarProjection A).app n p = w :=
      setActionBarFiberSection_projection A n w x
    rw [hpw] at hn
    exact hn

/-- 概要：任意の作用 bar の単体は語と始点の係数包含で復元される。
方針：作用圏の語の座標の左逆を使う。
規約：KST Lemma A.4。使われ方：線形な bar 写像の両端条件。 -/
lemma setActionBarFiberSection_reconstruct (A : SimplicialSetAction G X)
    (n : SimplexCategoryᵒᵖ) (p : (setActionBar A).obj n) :
    setActionBarFiberSection A n ((setActionBarProjection A).app n p) (p.obj 0).val = p := by
  letI := A.actionStructure n
  exact (actionNerveWordEquiv (G := G.obj n) (X := X.obj n) n.unop.len).symm_apply_apply p

/-- 概要：任意の作用 bar の単体の始点は単体射で prefix の作用を受ける。
方針：始点から像の最初の頂点までの作用圏の射の条件を使う。
規約：KST Lemma A.4。使われ方：線形区間写像の単体的自然性。 -/
lemma setActionBar_map_source (A : SimplicialSetAction G X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (p : (setActionBar A).obj n) :
    (((setActionBar A).map f p).obj 0).val =
      X.map f (A.action n (barWordFacePrefix f ((setActionBarProjection A).app n p))
        (p.obj 0).val) := by
  letI := A.actionStructure n
  change X.map f (p.obj (f.unop.toOrderHom 0)).val =
    X.map f (A.action n (p.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))).val (p.obj 0).val)
  exact congrArg (X.map f) (p.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))).property.symm

/-- 概要：作用 bar の射影は単体射と可換。
方針：射影の自然性を各単体で評価する。
規約：KST Lemma A.4。使われ方：線形区間写像で固定する語の移送。 -/
lemma setActionBar_map_projection (A : SimplicialSetAction G X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (p : (setActionBar A).obj n) :
    (setActionBarProjection A).app m ((setActionBar A).map f p) =
      (monoidBar G).map f ((setActionBarProjection A).app n p) :=
  congrArg (fun q ↦ q p) ((setActionBarProjection A).naturality f)

end SerrePositivity.KST.ProExcision
