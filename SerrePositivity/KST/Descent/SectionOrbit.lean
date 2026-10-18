module

public import SerrePositivity.KST.Descent.FiniteCoproduct
public import SerrePositivity.KST.Descent.ReductionFunctor
public import Mathlib.Algebra.Group.Action.Basic

/-!
# 切断の有限非交和からの軌道射

## 概要
分離射の有限個の切断から、標準の非交和を源とする有限・固有射を構成する。
切断の始域が被約なら、切断を終域の被約化へ持ち上げた射についても証明する。

## 方針
各切断の閉埋め込み性と、有限個の有限射の非交和の有限性を使う。
被約化への持ち上げが依然として切断であることは、包含との合成公式から示す。

## 規約
像が終域を覆うことや、一致中心の外で同型であることは有限性とは区別する。
このファイルの有限性は、その全射性や主定理の結論を仮定しない。

## 使われ方
論文 定理 3.1 の W = ⊔_I Y → V = (X ×_S Y)_red の幾何的な構成。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {I : Type u} {X Y : Scheme.{u}}

/-- 概要：同じ始域からの射の族を非交和からの一つの射にする（定理 3.1）。
方針：標準の圏論的非交和の desc を使う。
規約：有限性は定義に要求しない。
使われ方：translated section からの軌道射。 -/
noncomputable def sectionOrbitMap (sections : I → (X ⟶ Y)) : (∐ fun _ : I ↦ X) ⟶ Y :=
  Sigma.desc sections

/-- 概要：軌道射の各成分への制限は指定された切断（定理 3.1）。
方針：非交和の包含と desc の合成公式。
規約：指定したスキームの射の等式。
使われ方：群作用・基底の構造射との可換性。 -/
@[reassoc (attr := simp)] theorem sectionOrbitMap_component
    (sections : I → (X ⟶ Y)) (i : I) :
    Sigma.ι (fun _ : I ↦ X) i ≫ sectionOrbitMap sections = sections i :=
  Sigma.ι_comp_desc _ _

/-- 概要：分離射の有限個の切断からの軌道射は有限（定理 3.1）。
方針：切断の閉埋め込み性を有限性に移し、有限非交和の補題を適用する。
規約：切断の像の被覆や互いに素であることは要求しない。
使われ方：抽象 blowup に入力する軌道射の固有性。 -/
theorem sectionOrbitMap_isFinite [Finite I] (p : Y ⟶ X) [IsSeparated p]
    (sections : I → (X ⟶ Y)) (section_identity : ∀ i, sections i ≫ p = 𝟙 X) :
    IsFinite (sectionOrbitMap sections) := by
  have (i : I) : IsClosedImmersion (sections i) :=
    closedImmersion_of_section p (sections i) (section_identity i)
  exact finiteCoproductDesc_isFinite sections

/-- 概要：分離射の有限個の切断からの軌道射は固有（定理 3.1）。
方針：証明した有限性から固有性を得る。
規約：元の射 p の固有性は不要。
使われ方：軌道正方形の固有な辺。 -/
theorem sectionOrbitMap_isProper [Finite I] (p : Y ⟶ X) [IsSeparated p]
    (sections : I → (X ⟶ Y)) (section_identity : ∀ i, sections i ≫ p = 𝟙 X) :
    IsProper (sectionOrbitMap sections) := by
  have := sectionOrbitMap_isFinite p sections section_identity
  infer_instance

/-- 概要：被約な始域からの切断を終域の reduction へ持ち上げても切断（定理 3.1）。
方針：包含との合成を元の切断に戻す。
規約：被約な始域を仮定し、非被約な任意の射の因子分解は要求しない。
使われ方：V_red 上で各 translated section の閉埋め込み性を検証する。 -/
theorem reducedSection_identity [IsReduced X] (p : Y ⟶ X) (s : X ⟶ Y)
    (section_identity : s ≫ p = 𝟙 X) :
    schemeReductionLift s ≫ (schemeReductionInclusion Y ≫ p) = 𝟙 X := by
  rw [schemeReductionLift_comp_inclusion_assoc, section_identity]

/-- 概要：reduction への持ち上げから作る軌道射（定理 3.1 の W → V）。
方針：各切断の普遍的な持ち上げの非交和を取る。
規約：始域の被約性を明示する。
使われ方：被約化したファイバー積へ向かう実際のスキームの射。 -/
noncomputable def reducedSectionOrbitMap [IsReduced X] (sections : I → (X ⟶ Y)) :
    (∐ fun _ : I ↦ X) ⟶ schemeReduction Y :=
  sectionOrbitMap (fun i ↦ schemeReductionLift (sections i))

/-- 概要：持ち上げた軌道射と包含の合成は元の軌道射（定理 3.1）。
方針：非交和の各成分上で持ち上げの合成公式を使う。
規約：元の射との自然な比較を保持する。
使われ方：軌道射の像と、幾何的推移性による全射性の比較。 -/
@[reassoc (attr := simp)] theorem reducedSectionOrbitMap_comp_inclusion [IsReduced X]
    (sections : I → (X ⟶ Y)) :
    reducedSectionOrbitMap sections ≫ schemeReductionInclusion Y = sectionOrbitMap sections := by
  apply Sigma.hom_ext
  intro i
  simp [reducedSectionOrbitMap]

/-- 概要：reduction への有限切断の軌道射は有限（論文 定理 3.1）。
方針：包含と p の合成が分離であることと、持ち上げ後も切断であることを使う。
規約：元の Y が被約である必要はない。
使われ方：W → (X ×_S Y)_red の有限性。 -/
theorem reducedSectionOrbitMap_isFinite [Finite I] [IsReduced X]
    (p : Y ⟶ X) [IsSeparated p] (sections : I → (X ⟶ Y))
    (section_identity : ∀ i, sections i ≫ p = 𝟙 X) :
    IsFinite (reducedSectionOrbitMap sections) :=
  sectionOrbitMap_isFinite (schemeReductionInclusion Y ≫ p)
    (fun i ↦ schemeReductionLift (sections i))
    (fun i ↦ reducedSection_identity p (sections i) (section_identity i))

/-- 概要：群元によるコピーの置換を非交和の自己同型にする（論文 定理 3.1）。
方針：各コピーを g 倍の添字のコピーへ恒等射で写し、逆元で逆写像を作る。
規約：各コピー X 自身には自明に作用する。
使われ方：W = ⊔_I X の幾何的な置換作用。 -/
noncomputable def sectionOrbitPermutation {G : Type*} [Group G] [MulAction G I]
    (X : Scheme.{u}) (g : G) : (∐ fun _ : I ↦ X) ≅ (∐ fun _ : I ↦ X) where
  hom := Sigma.desc fun i ↦ Sigma.ι (fun _ : I ↦ X) (g • i)
  inv := Sigma.desc fun i ↦ Sigma.ι (fun _ : I ↦ X) (g⁻¹ • i)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    simp
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    simp

/-- 概要：コピーの置換による非交和上の G 作用（論文 定理 3.1）。
方針：群作用の乗法則を、各成分の包含との合成で検査する。
規約：Aut の積は関数の合成と同じ順序。
使われ方：軌道射の同変性と前層の置換表現との接続。 -/
noncomputable def sectionOrbitAction (G : Type*) [Group G] [MulAction G I]
    (X : Scheme.{u}) : G →* Aut (∐ fun _ : I ↦ X) where
  toFun g := Aut.of (sectionOrbitPermutation X g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply Sigma.hom_ext
    intro i
    simp [sectionOrbitPermutation]
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply Sigma.hom_ext
    intro i
    simp [sectionOrbitPermutation, Aut.mul_asIso, mul_smul]

/-- 概要：section の族の同変性から軌道射の同変性を得る（論文 定理 3.1）。
方針：各成分上で仮定の指定可換式を使う。
規約：作用はコピーを g 倍の添字に写す左作用。
使われ方：軌道正方形の同変な長完全列。 -/
theorem sectionOrbitMap_equivariant {G : Type*} [Group G] [MulAction G I]
    (sections : I → (X ⟶ Y)) (action : G →* Aut Y)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) (g : G) :
    (sectionOrbitAction G X g).asIso.hom ≫ sectionOrbitMap sections =
      sectionOrbitMap sections ≫ (action g).asIso.hom := by
  apply Sigma.hom_ext
  intro i
  simpa [sectionOrbitAction, sectionOrbitPermutation] using equivariant g i

/-- 概要：reduction への軌道射も誘導された G 作用に関して同変（定理 3.1）。
方針：包含の mono 性で消去し、元の軌道射と包含の同変性に還元する。
規約：各コピーの被約性が持ち上げを可能にする。
使われ方：被約化した V への同変な軌道射。 -/
theorem reducedSectionOrbitMap_equivariant [IsReduced X]
    {G : Type*} [Group G] [MulAction G I]
    (sections : I → (X ⟶ Y)) (action : G →* Aut Y)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) (g : G) :
    (sectionOrbitAction G X g).asIso.hom ≫ reducedSectionOrbitMap sections =
      reducedSectionOrbitMap sections ≫ (schemeReductionAction action g).asIso.hom := by
  apply (cancel_mono (schemeReductionInclusion Y)).mp
  simp only [Category.assoc, schemeReductionAction_comp_inclusion,
    reducedSectionOrbitMap_comp_inclusion, reducedSectionOrbitMap_comp_inclusion_assoc]
  exact sectionOrbitMap_equivariant sections action equivariant g

/-- 概要：像が全体を覆う section の族の被約化への軌道射は全射（定理 3.1）。
方針：元の軌道射で包含の像を持ち上げ、包含の点単射性で等式を反映する。
規約：像の被覆条件は明示する。幾何的推移性からの導出は別に必要。
使われ方：軌道射の全射性を reduction と両立させる。 -/
theorem reducedSectionOrbitMap_surjective [IsReduced X]
    (sections : I → (X ⟶ Y))
    (covering : ⋃ i, Set.range (sections i) = Set.univ) :
    Surjective (reducedSectionOrbitMap sections) := by
  have original : Surjective (sectionOrbitMap sections) :=
    Surjective.sigmaDesc_of_union_range_eq_univ covering
  constructor
  intro y
  obtain ⟨w, hw⟩ := original.surj (schemeReductionInclusion Y y)
  refine ⟨w, (schemeReductionInclusion Y).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, reducedSectionOrbitMap_comp_inclusion]
  exact hw

end SerrePositivity.KST.Descent
