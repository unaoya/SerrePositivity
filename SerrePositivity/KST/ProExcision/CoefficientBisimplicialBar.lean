module
public import SerrePositivity.KST.ProExcision.ConstantActionBar
public import SerrePositivity.KST.ProExcision.ActionBarRow

/-!
# 係数作用 bar の二重単体的模型

概要：bar 次数と係数の単体次数を分離した E_BH G を作る。
方針：各係数次数の離散作用 bar を束ね、対角を既存模型と同定する。
規約：KST Proposition A.1 の証明の二重単体的集合。
使われ方：各行の有限積の比較を対角へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：各係数次数の離散作用 bar を束ねた二重単体的集合。
方針：単体射で元の作用の同変条件を用いる。
規約：KST Proposition A.1 の E_BH G。使われ方：各行の有限積による同値性判定。 -/
def coefficientBisimplicialBar (A : SimplicialMonoidAction G H) : SimplicialObject SSet.{u} where
  obj n := discreteCoefficientActionBar (G.obj n) (H.obj n) (A.action n)
  map f := discreteCoefficientActionBarMap (G.map f).hom (H.map f).hom (A.naturality f)
  map_id n := by
    simp only [G.map_id, H.map_id]
    exact discreteCoefficientActionBarMap_id (A.action n)
  map_comp f g := by
    simp only [G.map_comp, H.map_comp]
    exact discreteCoefficientActionBarMap_comp _ _ _ _ _ _

/-- 概要：二重係数作用 bar の対角は既存の E_BH G と同型。
方針：全ての単体次数で同じ作用圏の射列となることを評価する。
規約：KST Proposition A.1。使われ方：行の証明と実際の対角比較の接続。 -/
def coefficientBisimplicialBarDiagonalIso (A : SimplicialMonoidAction G H) :
    Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (coefficientBisimplicialBar A) ≅
      coefficientActionBar A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; rfl)

/-- 概要：二重係数作用 bar の bar 次数 r の行は H^r×G^r。
方針：作用圏の始点とラベル列を取り、始点である BH の単体にも Segal 座標を使う。
規約：KST Proposition A.1 の証明。原典の G^r×H^r とは因子の順序が逆。
使われ方：各行の比較を有限個の作用写像で解析する。 -/
def coefficientBisimplicialBarRowIso (A : SimplicialMonoidAction G H) (r : ℕ) :
    (coefficientBisimplicialBar A).flip.obj (op ⦋r⦌) ≅
      monoidTupleSpace H r ⊗ monoidTupleSpace G r :=
  NatIso.ofComponents (fun n ↦ by
    let Ac := constantSimplicialMonoidAction (G.obj n) (H.obj n) (A.action n)
    letI : MulAction (G.obj n) ((nerve (SingleObj (H.obj n))) _⦋r⦌) :=
      (barSetAction Ac).actionStructure (op ⦋r⦌)
    exact ((actionNerveEquiv (G := G.obj n)
      (X := (nerve (SingleObj (H.obj n))) _⦋r⦌) r).trans
        (Equiv.prodCongr (monoidWordEquiv (H.obj n) r) (Equiv.refl _))).toIso) (by
          intro n m f
          apply ConcreteCategory.hom_ext
          intro p
          rfl)

/-- 概要：定数モノイドの単体的 bar は通常の一対象圏の nerve。
方針：係数方向の定数な恒等写像を評価する。
規約：KST Proposition A.1。使われ方：各係数次数の比較射の終域。 -/
def constantMonoidBarIso (M : MonCat.{u}) :
    monoidBar ((Functor.const SimplexCategoryᵒᵖ).obj M) ≅ nerve (SingleObj M) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; rfl)

/-- 概要：各係数次数の作用 bar から半直積 nerve への比較。
方針：定数単体的作用の transport 比較を通常の nerve へ移す。
規約：KST Proposition A.1、式 (A.3) の逆順の語の規約。
使われ方：二重単体的比較の成分。 -/
def coefficientBisimplicialBarComparisonApp (A : SimplicialMonoidAction G H)
    (n : SimplexCategoryᵒᵖ) :
    (coefficientBisimplicialBar A).obj n ⟶ (bisimplicialBar (simplicialActionProduct A)).obj n :=
  actionBarComparison (constantSimplicialMonoidAction (G.obj n) (H.obj n) (A.action n)) ≫
    (constantMonoidBarIso ((simplicialActionProduct A).obj n)).hom

/-- 概要：作用 bar と半直積 bar の二重単体的比較。
方針：各係数次数の transport 比較とそのラベルの自然性を使う。
規約：KST Proposition A.1。使われ方：各行の同値性から対角の同値性への移送。 -/
def coefficientBisimplicialBarComparison (A : SimplicialMonoidAction G H) :
    coefficientBisimplicialBar A ⟶ bisimplicialBar (simplicialActionProduct A) where
  app n := coefficientBisimplicialBarComparisonApp A n
  naturality n m f := by
    apply NatTrans.ext
    funext k
    letI := A.actionStructure n
    letI := A.actionStructure m
    let Ac := constantSimplicialMonoidAction (G.obj n) (H.obj n) (A.action n)
    letI := (barSetAction Ac).actionStructure k
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- 概要：二重単体的比較の対角は既存の transport 比較。
方針：各単体の射列への transport を評価する。
規約：KST Proposition A.1、式 (A.3)。
使われ方：各行の同値性の結論を実際の actionBarComparison へ移す。 -/
theorem coefficientBisimplicialBarComparison_diagonal (A : SimplicialMonoidAction G H) :
    (coefficientBisimplicialBarDiagonalIso A).hom ≫ actionBarComparison A =
      Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
        (Functor.uncurry.map (coefficientBisimplicialBarComparison A)) := by
  rfl

end SerrePositivity.KST.ProExcision
