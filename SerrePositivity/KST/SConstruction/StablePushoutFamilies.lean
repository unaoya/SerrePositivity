module
public import SerrePositivity.KST.SConstruction.StableSpanPushout
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-! # 安定な quasicategory の関手的な押し出しの族
概要：押し出し図式から任意 span への射影は trivial Kan fibration であり、厳密な切断を持つ。
方針：安定性からの全 span の余極限の存在を既存の相対補完へ供給する。
規約：単体的な族全体に対する射。使われ方：McCarthy 法の coherent pushout の選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：安定な quasicategory の押し出しの射影は全境界を持ち上げる。
方針：任意の入力 span の余極限の存在と押し出しの相対補完を使う。
規約：零次元を含み、追加の存在仮定は不要。使われ方：関手的な押し出しの選択。 -/
instance stable_pushoutProjection_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    TrivialKanFibration (pushoutProjection C) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨F, hF, hFd⟩ := exists_relative_pushoutFamily (boundary n).ι b a sq.w
    (fun v => stable_hasColimit_span _)
  exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFd }

/-- 概要：任意の部分で既に選んだ押し出しを保って span の族を補完できる。
方針：全 span の余極限の存在を既存の相対補完へ渡す。
規約：入力パラメーターに Kan 性や有限性は不要。使われ方：恒等図式の指定を保つ押し出しの選択。 -/
lemma exists_relative_stable_pushoutFamily {A B C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (a : A ⟶ pushoutDiagrams C) (ha : a ≫ pushoutProjection C = i ≫ d) :
    ∃ F : B ⟶ pushoutDiagrams C, i ≫ F = a ∧ F ≫ pushoutProjection C = d :=
  exists_relative_pushoutFamily i d a ha (fun _ => stable_hasColimit_span _)

/-- 概要：指定した部分の押し出しの選択は全 span 上の厳密な切断に延長できる。
方針：恒等な入力の族に相対補完を適用する。
規約：部分の包含は任意の単射。使われ方：pushout 関手の正規化。 -/
lemma exists_stablePushoutSection_extending {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (i : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) [Mono i]
    (a : A ⟶ pushoutDiagrams C) (ha : a ≫ pushoutProjection C = i) :
    ∃ s : (ihom (horn 2 0 : SSet.{u})).obj C ⟶ pushoutDiagrams C,
      i ≫ s = a ∧ s ≫ pushoutProjection C = 𝟙 _ :=
  exists_relative_stable_pushoutFamily i (𝟙 _) a (ha.trans (Category.comp_id _).symm)

/-- 概要：同じ入力 span の族の全押し出しの選択空間。
方針：内部 Hom による後合成の指定頂点の fiber を使う。
規約：高次の比較を含む単体集合。使われ方：関手的な選択の一意性。 -/
def stablePushoutFamilySpace {A C : SSet.{u}}
    (d : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) : SSet.{u} :=
  vertexFiber ((ihom A).map (pushoutProjection C)) (functorVertex d)

/-- 概要：任意のパラメーターを持つ押し出しの選択空間は可縮 Kan。
方針：内部 Hom での trivial Kan fibration の fiber の可縮性を使う。
規約：全 span 族に追加の存在仮定は不要。使われ方：選択によらない pushout の比較。 -/
lemma stablePushoutFamilySpace_isContractibleKan {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    IsContractibleKan (stablePushoutFamilySpace d) :=
  vertexFiber_isContractibleKan ((ihom A).map (pushoutProjection C)) (functorVertex d)

/-- 概要：同じ入力の族の二つの関手的な押し出しは関手として同型。
方針：trivial Kan fibration 上の持ち上げの比較を使う。
規約：頂点ごとの同型の集合に弱めない。使われ方：coherent な押し出しの選択の比較。 -/
def stablePushoutFamiliesIso {A C : SSet.{u}} [Quasicategory C] [IsStable C]
    (d : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) (F G : A ⟶ pushoutDiagrams C)
    (hF : F ≫ pushoutProjection C = d) (hG : G ≫ pushoutProjection C = d) : FunctorIso F G :=
  functorIsoOfTrivialKanFibration (pushoutProjection C) F G (hF.trans hG.symm)

/-- 概要：全ての span に押し出し四角形を単体的に選ぶ厳密な切断。
方針：trivial Kan fibration の切断を選ぶ。
規約：恒等図式での正規化は別に示す。使われ方：McCarthy 法の pushout 関手の入力。 -/
def stablePushoutSection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ pushoutDiagrams C :=
  Classical.choose (trivialKanFibration_exists_section (pushoutProjection C))

/-- 概要：関手的に選んだ押し出しは入力 span を厳密に回収する。
方針：切断の選択の仕様を使う。
規約：ホモトピー等号に弱めない。使われ方：押し出し族の二辺の回収。 -/
lemma stablePushoutSection_projection (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    stablePushoutSection C ≫ pushoutProjection C = 𝟙 _ :=
  Classical.choose_spec (trivialKanFibration_exists_section (pushoutProjection C))

/-- 概要：全 span に押し出しの頂点を関手的に選ぶ射。
方針：選んだ普遍四角形の (1,1) 頂点で評価する。
規約：単体的な族全体に定義する。使われ方：McCarthy 型の pushout 関手。 -/
def stablePushoutFunctor (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ C :=
  stablePushoutSection C ≫ (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

end SerrePositivity.KST.SConstruction
