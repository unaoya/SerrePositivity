module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenationCancellation
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionMapRepresentation

/-!
概要：全八水平合成は、因子の対象を固定すれば射の等式を反映する。
方針：有限単調射の共通表示へ送り、順序和・端点共有の因子を回収する。
規約：異なる切れ目を持つ分解の比較は別に扱う。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な語の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：minusから出る全ての射の区間表示は最小元を保つ。
方針：最小元保存のHomと実区間表示の二つの場合を照合する。
規約：非空の区間の0。使われ方：Riehl–Verity Proposition 3.1.10 の右因子の回収。 -/
lemma walkingAdjunctionOutgoingMap_zero {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    walkingAdjunctionOutgoingMap (Y := Y) f 0 = 0 := by
  cases Y
  · exact f.property
  · exact ordinalIntervalMap_zero (augmentedOrderHom f.unop)

/-- 概要：共通の全射の表示は同じ端点の元の射の等式を反映する。
方針：対象の等式を恒等として既存の異種等式の回収を使う。
規約：同じHom圏。使われ方：Riehl–Verity Proposition 3.1.10 の射の回収。 -/
lemma walkingAdjunctionOrderHom_injective {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} :
    Function.Injective (walkingAdjunctionOrderHom (X := X) (Y := Y) (A := A) (B := B)) := by
  intro f g h
  exact eq_of_heq (walkingAdjunctionOrderHom_hext rfl rfl f g (heq_of_eq h))

/-- 概要：minusに入る区間の表示も元の射の等式を反映する。
方針：共通の表示への異種等式を経由する。規約：同じ区間の次元。
使われ方：Riehl–Verity Proposition 3.1.10 の左因子の回収。 -/
lemma walkingAdjunctionIncomingMap_injective {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} :
    Function.Injective (walkingAdjunctionIncomingMap (X := X) (A := A) (B := B)) := by
  intro f g h
  apply eq_of_heq (walkingAdjunctionOrderHom_hext rfl rfl f g ?_)
  exact (walkingAdjunctionIncomingMap_heq f).symm.trans
    ((heq_of_eq h).trans (walkingAdjunctionIncomingMap_heq g))

/-- 概要：minusから出る区間の表示も元の射の等式を反映する。
方針：共通の表示の忠実性に移す。規約：同じ区間の次元。
使われ方：Riehl–Verity Proposition 3.1.10 の右因子の回収。 -/
lemma walkingAdjunctionOutgoingMap_injective {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} :
    Function.Injective (walkingAdjunctionOutgoingMap (Y := Y) (A := A) (B := B)) := by
  intro f g h
  apply eq_of_heq (walkingAdjunctionOrderHom_hext rfl rfl f g ?_)
  exact (walkingAdjunctionOutgoingMap_heq f).symm.trans
    ((heq_of_eq h).trans (walkingAdjunctionOutgoingMap_heq g))

/-- 概要：plusを経由する水平合成の射の等式から両因子の射を回収する。
方針：順序和の共通表示と二つの包含での消去則を使う。
規約：因子の対象を固定する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionHorizontal_plus_map_inj (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .plus} {B B' : walkingAdjunctionHom .plus Z}
    (f f' : A ⟶ A') (g g' : B ⟶ B')
    (h : (walkingAdjunctionHorizontal X .plus Z).map (X := (A, B)) (Y := (A', B')) (f, g) =
      (walkingAdjunctionHorizontal X .plus Z).map (X := (A, B)) (Y := (A', B')) (f', g')) :
    f = f' ∧ g = g' := by
  have hh := congrArg (fun k => walkingAdjunctionOrderHom (X := X) (Y := Z) k) h
  have hm := (walkingAdjunctionOrderHom_comp_plus X Z f g).symm.trans
    ((heq_of_eq hh).trans (walkingAdjunctionOrderHom_comp_plus X Z f' g'))
  obtain ⟨hf, hg⟩ := ordinalAppend_inj (eq_of_heq hm)
  exact ⟨walkingAdjunctionOrderHom_injective hf, walkingAdjunctionOrderHom_injective hg⟩

/-- 概要：minusを経由する水平合成の射の等式から両因子の射を回収する。
方針：共有点の右因子の最小元保存を明示し、端点共有の消去則を使う。
規約：因子の対象は固定。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionHorizontal_minus_map_inj (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .minus} {B B' : walkingAdjunctionHom .minus Z}
    (f f' : A ⟶ A') (g g' : B ⟶ B')
    (h : (walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f, g) =
      (walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f', g')) :
    f = f' ∧ g = g' := by
  have hh := congrArg (fun k => walkingAdjunctionOrderHom (X := X) (Y := Z) k) h
  have hm := (walkingAdjunctionOrderHom_comp_minus X Z f g).symm.trans
    ((heq_of_eq hh).trans (walkingAdjunctionOrderHom_comp_minus X Z f' g'))
  obtain ⟨hf, hg⟩ := ordinalGlue_inj
    (walkingAdjunctionOutgoingMap_zero g) (walkingAdjunctionOutgoingMap_zero g') (eq_of_heq hm)
  exact ⟨walkingAdjunctionIncomingMap_injective hf, walkingAdjunctionOutgoingMap_injective hg⟩

/-- 概要：全八水平合成の実双関手は忠実。
方針：中点の二つの場合と射の両因子の回収を使う。
規約：これは積の各固定Hom上の忠実性。使われ方：Riehl–Verity Proposition 3.1.10。 -/
instance walkingAdjunctionHorizontal_faithful (X Y Z : WalkingAdjunctionPoint) :
    (walkingAdjunctionHorizontal X Y Z).Faithful where
  map_injective {P Q} p q h := by
    rcases P with ⟨A, B⟩
    rcases Q with ⟨A', B'⟩
    rcases p with ⟨f, g⟩
    rcases q with ⟨f', g'⟩
    cases Y
    · exact Prod.ext_iff.mpr (walkingAdjunctionHorizontal_plus_map_inj X Z f f' g g' h)
    · exact Prod.ext_iff.mpr (walkingAdjunctionHorizontal_minus_map_inj X Z f f' g g' h)

/-- 概要：対象の等式を輸送しても、水平合成の射の異種等式から両因子を回収できる。
方針：対象を同一視し、実双関手の忠実性を使う。
規約：四つの対象の移送を明示する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionHorizontal_map_hext (X Y Z : WalkingAdjunctionPoint)
    {A B A' B' : walkingAdjunctionHom X Y} {C D C' D' : walkingAdjunctionHom Y Z}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (f : A ⟶ B) (f' : A' ⟶ B') (g : C ⟶ D) (g' : C' ⟶ D')
    (h : HEq ((walkingAdjunctionHorizontal X Y Z).map (X := (A, C)) (Y := (B, D)) (f, g))
      ((walkingAdjunctionHorizontal X Y Z).map (X := (A', C')) (Y := (B', D')) (f', g'))) :
    HEq f f' ∧ HEq g g' := by
  subst A'
  subst B'
  subst C'
  subst D'
  have hp := (walkingAdjunctionHorizontal X Y Z).map_injective (eq_of_heq h)
  exact ⟨heq_of_eq (congrArg Prod.fst hp), heq_of_eq (congrArg Prod.snd hp)⟩

/-- 概要：各頂点で二つの因子の対象が同じなら、全水平分解の射の部分も一意。
方針：合成関手の等式から各射の異種等式を取り出し、忠実性で両因子へ戻す。
規約：任意の添字圏の全射を含む。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionHorizontal_functor_inj {I : Type*} [Category I]
    (X Y Z : WalkingAdjunctionPoint)
    (F F' : I ⥤ walkingAdjunctionHom X Y) (G G' : I ⥤ walkingAdjunctionHom Y Z)
    (hF : ∀ i, F.obj i = F'.obj i) (hG : ∀ i, G.obj i = G'.obj i)
    (h : F.prod' G ⋙ walkingAdjunctionHorizontal X Y Z =
      F'.prod' G' ⋙ walkingAdjunctionHorizontal X Y Z) : F = F' ∧ G = G' := by
  have he {D : Type} [SmallCategory D] {K L : I ⥤ D} (hk : K = L)
      {i j : I} (f : i ⟶ j) : HEq (K.map f) (L.map f) := by
    cases hk
    rfl
  have hm {i j : I} (f : i ⟶ j) : HEq (F.map f) (F'.map f) ∧ HEq (G.map f) (G'.map f) := by
    exact walkingAdjunctionHorizontal_map_hext X Y Z (hF i) (hF j) (hG i) (hG j)
      (F.map f) (F'.map f) (G.map f) (G'.map f)
      (he (K := F.prod' G ⋙ walkingAdjunctionHorizontal X Y Z)
        (L := F'.prod' G' ⋙ walkingAdjunctionHorizontal X Y Z) h f)
  exact ⟨CategoryTheory.Functor.hext hF (fun _ _ f => (hm f).1),
    CategoryTheory.Functor.hext hG (fun _ _ f => (hm f).2)⟩

end SerrePositivity.InfinityCategories.HA.Monads
