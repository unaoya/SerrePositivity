module

public import SerrePositivity.KST.Comparison.PartialSectionInclusion

/-!
# 部分切断の写像の随伴表示

概要：部分切断の対象への写像を、引き戻した対象からの実際の切断で表す。
方針：引き戻しの第一成分を随伴の逆で戻し、条件・自然性・一意性を計算する。
規約：Segal 1974 Lemma 1.7 の単射に沿う延長の普遍性への補助。
使われ方：制限した部分切断と元の全空間の引き戻しの同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：部分切断の対象への写像に対応する、基底変換後の切断。
方針：引き戻しの第一成分を右随伴から戻す。
規約：定義域は B 上の任意の対象。
使われ方：部分切断の制限の普遍性。
-/
def partialSectionAdjunct {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A)
    {T : Over B} (r : T ⟶ partialSectionObject p q) : (sliceFiberFunctor p).obj T ⟶ Z :=
  ((Adjunction.ofIsLeftAdjoint (sliceFiberFunctor p)).homEquiv T Z).symm
    (r ≫ pullback.fst ((sliceFiberFunctor p).rightAdjoint.map q) (partialSectionUnit p))

/--
概要：随伴で戻した部分切断は、A への第二射影を持ち上げる。
方針：部分切断の引き戻しの可換性を随伴の逆で戻す。
規約：A→B の単射性はこの条件には不要。
使われ方：制限から復元した射の A 上での整合。
-/
theorem partialSectionAdjunct_comp {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A)
    {T : Over B} (r : T ⟶ partialSectionObject p q) :
    partialSectionAdjunct p q r ≫ q = pullback.snd T.hom p := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj := Adjunction.ofIsLeftAdjoint F
  let s := partialSectionUnit p
  let v := pullback.snd (G.map q) s
  have hcomm : (r ≫ pullback.fst (G.map q) s) ≫ G.map q = (r ≫ v) ≫ s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have h := congrArg ((adj.homEquiv T A).symm) hcomm
  rw [adj.homEquiv_naturality_right_symm] at h
  have hs : (adj.homEquiv _ _).symm s = pullback.snd (𝟙 B) p :=
    (adj.homEquiv _ _).symm_apply_apply _
  have hR : (adj.homEquiv T A).symm ((r ≫ v) ≫ s) =
      F.map (r ≫ v) ≫ pullback.snd (𝟙 B) p := by
    rw [adj.homEquiv_naturality_left_symm, hs]
  rw [hR] at h
  calc
    _ = F.map (r ≫ v) ≫ pullback.snd (𝟙 B) p := h
    _ = _ := sliceFiberFunctor_map_snd p (r ≫ v)

/--
概要：部分切断の随伴表示は、定義域の基底上の射の前合成に関して自然である。
方針：随伴の逆の左変数の自然性を使う。
規約：射は B 上で構造射を保つ。
使われ方：元の全空間からの包含との合成。
-/
theorem partialSectionAdjunct_naturality {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A)
    {S T : Over B} (i : S ⟶ T) (r : T ⟶ partialSectionObject p q) :
    partialSectionAdjunct p q (i ≫ r) =
      (sliceFiberFunctor p).map i ≫ partialSectionAdjunct p q r := by
  dsimp only [partialSectionAdjunct]
  rw [Category.assoc, Adjunction.homEquiv_naturality_left_symm]

/--
概要：元の全空間からの包含を随伴で戻すと、第一射影になる。
方針：包含の第一成分の式と随伴の逆の計算則を使う。
規約：A→B は単射とする。
使われ方：制限した部分切断から元の写像を復元する。
-/
theorem partialSectionAdjunct_inclusion {Z A B : SSet.{u}} (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    partialSectionAdjunct p q (partialSectionInclusionOver p q) = pullback.fst (q ≫ p) p := by
  dsimp only [partialSectionAdjunct]
  rw [partialSectionInclusionOver_fst]
  exact ((Adjunction.ofIsLeftAdjoint (sliceFiberFunctor p)).homEquiv _ _).symm_apply_apply _

/--
概要：部分切断の対象への二つの写像は、随伴表示が等しければ等しい。
方針：引き戻しの第一成分を随伴で等置し、終対象への第二成分の一意性を使う。
規約：A→B の単射性はこの一意性には不要。
使われ方：制限の引き戻しの普遍性の一意性。
-/
theorem partialSection_hom_ext {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A)
    {T : Over B} (r s : T ⟶ partialSectionObject p q)
    (h : partialSectionAdjunct p q r = partialSectionAdjunct p q s) : r = s := by
  apply pullback.hom_ext
  · apply ((Adjunction.ofIsLeftAdjoint (sliceFiberFunctor p)).homEquiv T Z).symm.injective
    exact h
  · exact (Over.mkIdTerminal (X := B)).hom_ext _ _

end SerrePositivity.KST.Comparison
