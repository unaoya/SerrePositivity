module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionCurry

/-!
概要：底と初期値を固定する実際の族を、任意の単射なパラメータ境界から延長する。
方針：元の族を可縮な相対延長空間へ戻し、その全境界持ち上げを raw な族へ展開する。
規約：元の境界族・底・初期値を同時に厳密に保つ。パラメータの Kan 性は不要。
使われ方：輸送比較の円柱や高次の境界を一つの整合する族として埋める。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 固定した底と初期値を持つ全パラメータ族は、任意の単射な境界から延長できる。 -/
lemma exists_fixedExtensionFamily_of_mono {A D K L E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (β : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (k : K ⟶ L) [Mono k] (W : A ⊗ K ⟶ E)
    (hW : W ≫ p = fst A K ≫ β) (hI : (i ▷ K) ≫ W = fst D K ≫ v) :
    ∃ U : A ⊗ L ⟶ E,
      U ≫ p = fst A L ≫ β ∧
      (i ▷ L) ≫ U = fst D L ≫ v ∧ (A ◁ k) ≫ U = W := by
  let X := relativeFunctorExtensionSpace p β i v hv
  have hX : IsContractibleKan X := relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv
  have : TrivialKanFibration (terminal.from X) :=
    (isContractibleKan_iff_trivialKanFibration X).mp hX
  have := TrivialKanFibration.mem (p := terminal.from X) k inferInstance
  let sq : CommSq (fixedExtensionCurry p β i v hv W hW hI) k
      (terminal.from X) (terminal.from L) := ⟨terminal.hom_ext _ _⟩
  let t := sq.lift ≫ relativeFunctorExtensionSpaceι p β i v hv
  refine ⟨relativeFunctorUncurry t, relativeFunctorUncurry_projection t, ?_, ?_⟩
  · rw [← relativeFunctorUncurry_pre]
    change relativeFunctorUncurry
      ((sq.lift ≫ relativeFunctorExtensionSpaceι p β i v hv) ≫ relativeFunctorPre p β i) = _
    rw [Category.assoc, relativeFunctorExtensionSpaceι_pre]
    change uncurry ((sq.lift ≫ SSet.const (relativeFunctorVertex p (i ≫ β) v hv)) ≫
      vertexFiberι ((ihom D).map p) (functorVertex (i ≫ β))) = _
    rw [SSet.comp_const, SSet.const_comp]
    exact uncurry_const_functorVertex v
  · rw [← relativeFunctorUncurry_parameter]
    change relativeFunctorUncurry
      (k ≫ (sq.lift ≫ relativeFunctorExtensionSpaceι p β i v hv)) = W
    rw [← Category.assoc, sq.fac_left, fixedExtensionCurry_uncurry]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
