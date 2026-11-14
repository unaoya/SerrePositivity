module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechVertexFrame
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderBigComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechVertexFrame
import all SerrePositivity.HomologicalAlgebra.Cech.BaseChange

/-!
# 選んだ Čech–Alexander 包と有限 affine 枠の比較

## 概要
HasEnvelopes から選んだ複体を、既存の大きい頂点枠を経由して有限 affine 枠と比較する。
## 方針
大きい枠の二つの site 表示を同型にし、⑤b の toBig_quasiIso をそのまま使う。
## 規約
BS 著者版 Construction 4.18・Remark 4.19。新しい比較ホモトピーは作らない。
## 使われ方
原典の選択した模型と有限変数による計算模型の通常の複体としての照合。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (Q : Poly (A ⧸ P.ideal)) {κ : Cardinal.{u}}
variable (E : ∀ (Q' : Poly (A ⧸ P.ideal)) n, BigCechTerm P Q' n)
variable (hb : ∀ n, IsBoundedPrism (E Q n).prism)
variable (hs : ∀ n, Cardinal.mk (E Q n).carrier ≤ κ)

/-- 大きい頂点枠の site 表示と、変数の普遍性から組み立てた site 表示の自然同型。 -/
def bigCechVertexSiteIso :
    BigCechVertexFrame.model P Q E hb hs ≅ bigCechSiteAlexander (E Q) hb hs :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n θ
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact (bigCechSiteAlexander_map (E Q) hb hs θ).symm)

variable (h : HasEnvelopes P (polyCompletion P Q.n)) (hκ : cutoff A (polyCompletion P Q.n) ≤ κ)

/-- 選んだ包絡の余単体的対象は、既存の大きい頂点枠に自然に同型。 -/
def cechAlexanderVertexSiteIso :
    cechAlexander P (polyCompletion P Q.n) h κ hκ ≅ BigCechVertexFrame.model P Q E hb hs :=
  cechAlexanderBigSiteIso P h hκ (E Q) hb hs ≪≫ (bigCechVertexSiteIso P Q E hb hs).symm

/-- 同じ基底の下の環から加群を取る二つの既存の関手の照合。 -/
def cechUnderlyingModuleIso :
    Cech.underToModule (CommRingCat.of A) ≅ PDCechNerve.algebraModule A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ _; rfl)

local notation "G" => prismSiteAlgebras P (polyCompletion P Q.n) κ ⋙ PDCechNerve.algebraModule A

/-- 選んだ包絡の実際の交代余面複体と大きい頂点枠の複体の同型。 -/
def cechAlexanderVertexComplexIso :
    cechAlexanderComplex P (polyCompletion P Q.n) κ h hκ ≅
      (alternatingCofaceMapComplex _).obj (BigCechVertexFrame.model P Q E hb hs ⋙ G) :=
  (alternatingCofaceMapComplex _).mapIso
    ((Functor.isoWhiskerLeft
      (cechAlexander P (polyCompletion P Q.n) h κ hκ ⋙ prismSiteAlgebras P (polyCompletion P Q.n) κ)
      (cechUnderlyingModuleIso (A := A))) ≪≫
      Functor.isoWhiskerRight (cechAlexanderVertexSiteIso P Q E hb hs h hκ) G)

variable (U : ∀ n, AffineEnvelopeTerm P Q.n n κ)

/-- 概要：有限 affine 枠から選んだ包絡の複体への比較は擬同型。
方針：既存の toBig_quasiIso を複体の同型で移す。
規約：BS 著者版 Remark 4.19。使われ方：原典の模型の選択に依らない古典的な入力。 -/
theorem affineToChosenCech_quasiIso :
    QuasiIso ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (BigCechVertexFrame.toBig P Q E hb hs U) G) ≫
      (cechAlexanderVertexComplexIso P Q E hb hs h hκ).inv) := by
  let := BigCechVertexFrame.toBig_quasiIso P Q E hb hs U
  infer_instance

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.18" (partial := component) "大きい枠の Čech–Alexander 模型の項と座標変換（BS-D69 P2）。Δ を計算することは G9・G10 待ち ／ 11-11 更新 ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.affineToChosenCech_quasiIso
