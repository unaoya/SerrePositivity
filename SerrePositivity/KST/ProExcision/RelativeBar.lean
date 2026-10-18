module

public import SerrePositivity.KST.ProExcision.ActionMorphisms
public import SerrePositivity.KST.ProExcision.RelativeModule

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 半直積の相対 bar ホモロジーの代数部分

概要：基底の bar の分裂包含の余核を、相対項の具体的な加群として構成する。
方針：K-L2 が所有する関手を引数にとり、単体的モノイドの射の関手性で余核へ降ろす。
規約：F は所有レーンのホモロジー関手を受ける引数であり、H_* の新しい定義ではない。
使われ方：KST App. A の相対項、Lemma A.4 の自明射による零化。Prop A.1 との比較は別工程。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
variable {G H H' : SimplicialObject MonCat.{u}}

/-- 概要：半直積 bar の基底 bar の像による通常商。
方針：借用した関手 F の値の間の包含の余核を取る。
規約：F を H_i に特殊化するのは所有レーンの界面を受けたとき。
使われ方：KST Appendix A の相対ホモロジーの分裂余核模型。 -/
def relativeBarModule (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (A : SimplicialMonoidAction G H) :
    ModuleCat.{u} ℤ :=
  relativeModule (F.map (monoidBarMap (simplicialActionProductSection A)))

/-- 概要：基底 bar の包含は任意の関手の下でも射影で分裂する。
方針：半直積の分裂を bar と F の関手性で写す。
規約：F のホモトピー不変性は不要。使われ方：KST App. A の相対項を余核で表示する理由。 -/
theorem relativeBarSection_projection (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (A : SimplicialMonoidAction G H) :
    F.map (monoidBarMap (simplicialActionProductSection A)) ≫
      F.map (monoidBarMap (simplicialActionProductProjection A)) = 𝟙 _ := by
  rw [← F.map_comp, ← monoidBarMap_comp, simplicialActionProductSection_projection,
    monoidBarMap_id, F.map_id]

/-- 概要：基底 bar の F による像の包含は単射。
方針：bar の射影が左逆であることを各元へ適用する。
規約：相対加群の定義と独立に単射性を示す。
使われ方：KST App. A の split injection H_i(G) → H_i(G ⋉ H)。 -/
theorem relativeBarSection_injective (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (A : SimplicialMonoidAction G H) :
    Function.Injective (F.map (monoidBarMap (simplicialActionProductSection A))).hom := by
  apply Function.LeftInverse.injective (g :=
    (F.map (monoidBarMap (simplicialActionProductProjection A))).hom)
  intro x
  exact congrArg (fun f ↦ f.hom x) (relativeBarSection_projection F A)

/-- 概要：半直積の誘導射と基底 bar の包含の正方形は可換。
方針：単体的モノイドの包含との可換性を bar と F へ写す。
規約：基底の射は恒等。使われ方：KST Lemma A.4 の相対項の誘導射。 -/
theorem relativeBarMap_square (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    (f : SimplicialActionHom A B) :
    F.map (monoidBarMap (simplicialActionProductSection A)) ≫
        F.map (monoidBarMap (simplicialActionProductMap f)) =
      𝟙 (F.obj (monoidBar G)) ≫ F.map (monoidBarMap (simplicialActionProductSection B)) := by
  rw [← F.map_comp, ← monoidBarMap_comp, simplicialActionProductSection_map, Category.id_comp]

/-- 概要：同変射が相対 bar 項に誘導する線形写像。
方針：可換正方形を包含の像による商へ降ろす。
規約：F は所有レーンから受ける関手。使われ方：KST Lemma A.4 の相対ホモロジー写像。 -/
def relativeBarMap (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    (f : SimplicialActionHom A B) : relativeBarModule F A ⟶ relativeBarModule F B :=
  relativeModuleMap _ _ (𝟙 _) (F.map (monoidBarMap (simplicialActionProductMap f)))
    (relativeBarMap_square F f)

/-- 概要：自明な同変射は相対 bar 項で零を誘導する。
方針：半直積の自明射が基底の射影と包含を経由することを使う。
規約：Prop A.1 やホモトピー不変性を仮定しない代数部分。
使われ方：KST Lemma A.4 で C(e) と比較した後の相対項の零化。 -/
theorem relativeBarMap_trivial_zero (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (A : SimplicialMonoidAction G H) (B : SimplicialMonoidAction G H') :
    relativeBarMap F (SimplicialActionHom.trivial A B) = 0 := by
  apply relativeModuleMap_zero_of_factor _ _ _ _ _
    (F.map (monoidBarMap (simplicialActionProductProjection A)))
  rw [simplicialActionProductMap_trivial, monoidBarMap_comp, F.map_comp]

/-- 概要：絶対 bar 項で自明射と同じ写像は、相対 bar 項では零。
方針：余核上の誘導射の右側写像への依存性と自明射の零性を使う。
規約：絶対項の比較を入力とする代数部分であり、Lemma A.4 全体の証明ではない。
使われ方：Prop A.1 と m-ホモトピーによる絶対項の比較を相対項へ移す。 -/
theorem relativeBarMap_zero_of_absolute_eq_trivial (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    (f : SimplicialActionHom A B)
    (hf : F.map (monoidBarMap (simplicialActionProductMap f)) =
      F.map (monoidBarMap (simplicialActionProductMap (SimplicialActionHom.trivial A B)))) :
    relativeBarMap F f = 0 := by
  calc
    relativeBarMap F f = relativeBarMap F (SimplicialActionHom.trivial A B) :=
      relativeModuleMap_eq_of_right_eq _ _ _ _ _ _ _ _ hf
    _ = 0 := relativeBarMap_trivial_zero F A B

end SerrePositivity.KST.ProExcision
