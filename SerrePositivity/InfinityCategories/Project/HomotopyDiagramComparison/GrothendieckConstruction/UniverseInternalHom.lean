module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：単体集合の内部 Hom と宇宙の持ち上げを交換する標準同型。
方針：評価の ULift を curry し、ULift の完全忠実性で各パラメータの射の逆を作る。
規約：両因子は元の宇宙 u にあり、Kan 性は不要。
使われ方：HTT 4.2.4.1、可逆 path と導来 fiber の ULift の厳密な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：内部 Hom の ULift から両因子の ULift の内部 Hom への標準射。
方針：直積の ULift の同型と評価の ULift を curry する。
規約：元の評価を保持する比較射を固定する。
使われ方：可逆 path の通常の区間関手空間の宇宙の移送。 -/
def uliftInternalHomComparison (K B : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B) ⟶
      (ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj ((SSet.uliftFunctor.{v, u}).obj B) :=
  curry ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K ((ihom K).obj B)).inv ≫
    (SSet.uliftFunctor.{v, u}).map ((ihom.ev K).app B))

/-- 概要：標準比較を通じた族の展開は元の族の展開の ULift と可換。
方針：curry の逆関係と直積の ULift の第二因子の自然性を使う。
規約：パラメータ A も元の宇宙に置く。
使われ方：内部 Hom の標準比較の同型性と端点評価の照合。 -/
lemma uliftInternalHomComparison_map_uncurry {K B A : SSet.{u}}
    (f : A ⟶ (ihom K).obj B) :
    uncurry ((SSet.uliftFunctor.{v, u}).map f ≫ uliftInternalHomComparison K B) =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K A).inv ≫ (SSet.uliftFunctor.{v, u}).map (uncurry f) := by
  rw [uncurry_natural_left, uliftInternalHomComparison, uncurry_curry,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso_inv_whiskerLeft, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← uncurry_eq]

/-- 概要：内部 Hom への小さいパラメータの射と持ち上げた後の射は全単射に対応する。
方針：展開した族を直積同型で戻し、ULift の充満性で原像を取る。
規約：順射は元の射の ULift に標準比較を後合成した射。
使われ方：標準単体をパラメータにして各次数の全単射を得る。 -/
def uliftInternalHomHomEquiv (K B A : SSet.{u}) :
    (A ⟶ (ihom K).obj B) ≃
      ((SSet.uliftFunctor.{v, u}).obj A ⟶
        (ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj ((SSet.uliftFunctor.{v, u}).obj B)) where
  toFun f := (SSet.uliftFunctor.{v, u}).map f ≫ uliftInternalHomComparison K B
  invFun g := curry ((SSet.uliftFunctor.{v, u}).preimage
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K A).hom ≫ uncurry g))
  left_inv f := by
    apply uncurry_injective
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [uncurry_curry, CategoryTheory.Functor.map_preimage,
      uliftInternalHomComparison_map_uncurry, Iso.hom_inv_id_assoc]
  right_inv g := by
    apply uncurry_injective
    rw [uliftInternalHomComparison_map_uncurry, uncurry_curry,
      CategoryTheory.Functor.map_preimage, Iso.inv_hom_id_assoc]

/-- 概要：内部 Hom の ULift と持ち上げた内部 Hom の各次数は全単射。
方針：標準単体の Yoneda 表示とパラメータの射の全単射を合成する。
規約：標準単体の宇宙も同時に移す。
使われ方：標準比較の各成分の全単射性。 -/
def uliftInternalHomSimplexEquiv (K B : SSet.{u}) (n : ℕ) :
    ((SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B)) _⦋n⦌ ≃
      ((ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj
        ((SSet.uliftFunctor.{v, u}).obj B)) _⦋n⦌ :=
  Equiv.ulift.trans (SSet.yonedaEquiv.symm.trans
    ((uliftInternalHomHomEquiv K B Δ[n]).trans
      (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).homCongr (Iso.refl _)).trans SSet.yonedaEquiv)))

/-- 概要：各次数の全単射は実際の標準比較の成分と一致する。
方針：Yoneda 射の ULift と後合成の自然性を計算する。
規約：全単射の選択で比較射を変更しない。
使われ方：実際の標準比較の同型性を確認する。 -/
lemma uliftInternalHomSimplexEquiv_apply (K B : SSet.{u}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B)) _⦋n⦌) :
    uliftInternalHomSimplexEquiv K B n s =
      (uliftInternalHomComparison K B).app (Opposite.op ⦋n⦌) s := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).inv ≫
    (((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm s.down) ≫
      uliftInternalHomComparison K B) ≫ 𝟙 _)) = _
  rw [Category.comp_id, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  cases s
  rfl

/-- 概要：内部 Hom の ULift の標準比較は厳密な同型。
方針：各次数の全単射と実際の成分の一致を使う。
規約：Kan 性や fibration 性は不要。
使われ方：導来 fiber の path 成分の厳密な宇宙の比較。 -/
instance uliftInternalHomComparison_isIso (K B : SSet.{u}) :
    IsIso (uliftInternalHomComparison.{u, v} K B) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  change Function.Bijective (fun s ↦ (uliftInternalHomComparison K B).app _ s)
  have h : (fun s ↦ (uliftInternalHomComparison K B).app (Opposite.op ⦋n⦌) s) =
      uliftInternalHomSimplexEquiv K B n :=
    funext (fun s ↦ (uliftInternalHomSimplexEquiv_apply K B s).symm)
  rw [h]
  exact (uliftInternalHomSimplexEquiv K B n).bijective

/-- 概要：内部 Hom の ULift と持ち上げた二因子の内部 Hom の標準同型。
方針：構成済みの比較射の同型性から逆射を取る。
規約：順射は評価から作った標準比較そのもの。
使われ方：可逆 path の ULift と元の導来 fiber の復元。 -/
def uliftInternalHomIso (K B : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B) ≅
      (ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj ((SSet.uliftFunctor.{v, u}).obj B) :=
  asIso (uliftInternalHomComparison K B)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
