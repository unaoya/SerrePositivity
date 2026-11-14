module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.IntegerUnitizationMap
public import SerrePositivity.KST.ProExcision.Lemma416Relative

/-!
# 非単位単体環の標準の整数単位化模型

概要：非単位結合環の単体図式を最小のデータで表し、標準の単体的イデアル模型を構成する。
方針：各次数を整数単位化し、面・退化を証明済みの標準拡張で移す。
規約：KST Proposition 4.14・Lemma 4.16 の非単位非可換環。
使われ方：周囲環とイデアルの表示を外から仮定せずに実比較へ適用する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：非単位結合環を型と環構造に束ねる。
方針：Mathlib の非単位環とその準同型をそのまま用いる。
規約：KST 4.16 の最小の図式の対象。使われ方：非単位単体環の次数ごとの型。 -/
structure NonUnitalRingObject where
  of ::
  carrier : Type u
  [ring : NonUnitalRing carrier]

attribute [instance] NonUnitalRingObject.ring

/-- 概要：束ねた非単位環の台となる型。
方針：carrier を CoeSort として使う。
規約：KST 4.16。使われ方：次数間の非単位環準同型の型。 -/
instance nonUnitalRingObjectCoeSort : CoeSort NonUnitalRingObject (Type u) :=
  ⟨NonUnitalRingObject.carrier⟩

/-- 概要：非単位環の単体図式の最小データ。
方針：対象・非単位環準同型・恒等と合成の法則を明示する。
規約：通常の反変単体図式と同じデータ。π や H_* やホモトピーの結論は含めない。
使われ方：標準単位化による SimplicialIdealData の構成。 -/
structure NonUnitalSimplicialRing where
  obj : SimplexCategoryᵒᵖ → NonUnitalRingObject.{u}
  map {k l : SimplexCategoryᵒᵖ} : (k ⟶ l) → (obj k →ₙ+* obj l)
  map_id (k : SimplexCategoryᵒᵖ) : map (𝟙 k) = NonUnitalRingHom.id (obj k)
  map_comp {k l s : SimplexCategoryᵒᵖ} (φ : k ⟶ l) (ψ : l ⟶ s) :
    map (φ ≫ ψ) = (map ψ).comp (map φ)

/-- 概要：任意の非単位単体環から標準の単体的イデアル模型を構成する。
方針：整数単位化の標準拡張の恒等・合成と核イデアルの保存を使う。
規約：KST 4.16、非可換な非単位環に周囲環の追加の表示を仮定しない。
使われ方：単体的イデアル版 Lemma 4.16 を一般の非単位単体環に適用する。 -/
def NonUnitalSimplicialRing.standardIdeal (I : NonUnitalSimplicialRing.{u}) : SimplicialIdealData.{u} where
  ambient :=
    { obj := fun k ↦ RingCat.of (Unitization ℤ (I.obj k))
      map := fun φ ↦ RingCat.ofHom (integerUnitizationMap (I.map φ))
      map_id := by
        intro k
        apply RingCat.hom_ext
        change integerUnitizationMap (I.map (𝟙 k)) = RingHom.id _
        rw [I.map_id]
        exact integerUnitizationMap_id
      map_comp := by
        intro k l s φ ψ
        apply RingCat.hom_ext
        change integerUnitizationMap (I.map (φ ≫ ψ)) =
          (integerUnitizationMap (I.map ψ)).comp (integerUnitizationMap (I.map φ))
        rw [I.map_comp]
        exact integerUnitizationMap_comp _ _ }
  ideal k := integerUnitizationIdeal (I.obj k)
  map_mem φ x hx := integerUnitizationMap_ideal (I.map φ) x hx

/-- 概要：元の零次の指定元を標準単位化の核イデアルへ入れる。
方針：整数成分が零となる標準包含を使う。
規約：KST 4.16 の a∈I₀。使われ方：実帰納ホモトピーの標準の理想模型への入力。 -/
def NonUnitalSimplicialRing.standardElement (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) :
    I.standardIdeal.ideal (op ⦋0⦌) :=
  ⟨(a : Unitization ℤ (I.obj (op ⦋0⦌))), inr_mem_integerUnitizationIdeal _ a⟩

/-- 概要：一般の非単位単体環の標準模型における非可換版 Lemma 4.16。
方針：単位化と核イデアルを実際に構成し、証明済みの単体的理想模型の実比較を適用する。
規約：KST Lemma 4.16、φ(v)=va、全行列同変な実 m 次比較。
使われ方：A.4 と Claim 4.15 の相対零化の入力。 -/
def nonUnitalLemma416 (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n m : ℕ) :
    HomologicallyMConstant (I.standardIdeal.rightColumnActionHom (I.standardElement a) n m) m :=
  lemma416 I.standardIdeal (I.standardElement a) n m

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 4.16" (partial := component) "仮定：単体イデアルまたは非単位的単体環の行列・列作用（原典と一致）。結論：同変な m 次までの定値ホモトピーを行列模型で与える。原典の一般線形群の係数つき鎖への全比較を含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.nonUnitalLemma416
