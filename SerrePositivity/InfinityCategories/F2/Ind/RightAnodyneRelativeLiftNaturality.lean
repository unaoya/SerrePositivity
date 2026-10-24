module

public import SerrePositivity.InfinityCategories.F2.Ind.RightAnodyneRelativeLiftIso
public import
  SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexIsoMappingLaws

/-!
概要：元の right-anodyne 相対比較は、元の制限への像とさらに前合成した比較を保持する。
方針：指定等号同型の同じ充満忠実な逆像を取り、元の前合成の厳密な合成則で照合する。
規約：比較の存在だけでなく、元の指定同型そのものの値を保持する。
使われ方：終点比較を旧族で制限したときに、指定変換を同じ比較で回収する。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A T E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
  (b : A ⟶ B) (i : T ⟶ A) (hi : rightAnodyneExtensions i)
  (f g : A ⟶ E) (hf : f ≫ p = b) (hg : g ≫ p = b) (h : i ≫ f = i ≫ g)
omit [RightFibration p] in
include h in
/-- 概要：同じ元の指定制限は相対関手の頂点の等号を与える。
方針：全写像を照合。規約：指定制限の等号。使われ方：比較の指定像。 -/
lemma rightAnodyneRelativeLiftEndpointEq :
    (relativeFunctorPre p b i).app _ (relativeFunctorVertex p b f hf) =
      (relativeFunctorPre p b i).app _ (relativeFunctorVertex p b g hg) := by
  rw [relativeFunctorPre_vertex, relativeFunctorPre_vertex]
  apply Subtype.ext
  exact congrArg functorVertex h
/-- 概要：元の相対比較は元の指定制限で同じ等号同型を厳密に回収する。
方針：充満忠実な元の逆像。規約：指定値を保持。使われ方：旧族の比較の照合。 -/
lemma rightAnodyneRelativeLiftIso_map :
    VertexIso.map (rightAnodyneRelativeLiftIso p b i hi f g hf hg h)
      (relativeFunctorPre p b i) =
    eqToIso (congrArg SSet.HomotopyCategory.mk
      (rightAnodyneRelativeLiftEndpointEq p b i f g hf hg h)) := by
  unfold rightAnodyneRelativeLiftIso
  exact IsFullyFaithful.preimageVertexIso_map _ _
/-- 概要：同じ元の持ち上げの表示を等号で変更しても指定比較そのものを保持する。
方針：元の両端の等号を消去。規約：元の指定値。使われ方：厳密な全境界の表示変更。 -/
lemma rightAnodyneRelativeLiftIso_heq {f' g' : A ⟶ E}
    (hf' : f' ≫ p = b) (hg' : g' ≫ p = b) (h' : i ≫ f' = i ≫ g')
    (hff : f = f') (hgg : g = g') :
    HEq (rightAnodyneRelativeLiftIso p b i hi f g hf hg h)
      (rightAnodyneRelativeLiftIso p b i hi f' g' hf' hg' h') := by
  subst f'
  subst g'
  rfl
/-- 概要：元の right-anodyne 制限をさらに制限した比較は、同じ元の相対比較そのもの。
方針：指定像の一致を充満忠実に反映。規約：同じ指定同型。使われ方：旧族の変換保持。 -/
lemma rightAnodyneRelativeLiftIso_precomp {A₀ : SSet.{u}} (j : A₀ ⟶ A)
    (i₀ : T ⟶ A₀) (hi₀ : rightAnodyneExtensions i₀)
    (hij : rightAnodyneExtensions (i₀ ≫ j))
    (hh : (i₀ ≫ j) ≫ f = (i₀ ≫ j) ≫ g) :
    VertexIso.map (rightAnodyneRelativeLiftIso p b (i₀ ≫ j) hij f g hf hg hh)
      (relativeFunctorPre p b j) =
    rightAnodyneRelativeLiftIso p (j ≫ b) i₀ hi₀ (j ≫ f) (j ≫ g)
      (by rw [Category.assoc, hf]) (by rw [Category.assoc, hg])
      (by simpa only [Category.assoc] using hh) := by
  have := relativeFunctorPre_trivialKanFibration_of_rightAnodyne p (j ≫ b) i₀ hi₀
  have hff := (isQCatEquivalence_of_trivialKanFibration
    (relativeFunctorPre p (j ≫ b) i₀)).isFullyFaithful
  apply Iso.ext
  apply hff.toHoFullyFaithful.map_injective
  have hmap : VertexIso.map
      (VertexIso.map (rightAnodyneRelativeLiftIso p b (i₀ ≫ j) hij f g hf hg hh)
        (relativeFunctorPre p b j)) (relativeFunctorPre p (j ≫ b) i₀) =
      VertexIso.map (rightAnodyneRelativeLiftIso p (j ≫ b) i₀ hi₀ (j ≫ f) (j ≫ g)
        (by rw [Category.assoc, hf]) (by rw [Category.assoc, hg])
        (by simpa only [Category.assoc] using hh)) (relativeFunctorPre p (j ≫ b) i₀) := by
    rw [VertexIso.map_comp]
    refine (VertexIso.map_congr
      (rightAnodyneRelativeLiftIso p b (i₀ ≫ j) hij f g hf hg hh)
      (relativeFunctorPre_comp p b j i₀)).trans ?_
    rw [rightAnodyneRelativeLiftIso_map, rightAnodyneRelativeLiftIso_map]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans]
  exact congrArg Iso.hom hmap
end SerrePositivity.InfinityCategories.F2.Ind
