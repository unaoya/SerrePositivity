module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
概要：制限された複体への射を、零延長した始域からの射に拡張する。
方針：埋め込みの像では標準の成分同型を使い、像の外では零射を取る。
規約：像の外へ出る微分で消える条件を具体的な境界条件とする。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の自然数鎖複体から整数複体への包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') [e.IsRelIff]
  {L : HomologicalComplex C c} {K : HomologicalComplex C c'} (φ : L ⟶ K.restriction e)

open scoped Classical in
/--
概要：零延長した始域からの射の成分。
方針：像の中では成分同型を介して元の射を使い、外では零射とする。
規約：埋め込みの像の表示を選択する。
使われ方：Stacks 19.12.2、TT §3 の整数次数への延長。
-/
def descFromExtendedComplexComponent (i' : ι') : (L.extend e).X i' ⟶ K.X i' :=
  if h : ∃ i, e.f i = i' then
    (L.extendXIso e h.choose_spec).hom ≫ φ.f h.choose ≫
      (K.restrictionXIso e h.choose_spec).hom else 0

/--
概要：像の中の延長成分は指定した表示の標準式に一致する。
方針：埋め込みの単射性で選択した添字を同定する。
規約：表示の等式の証明には依存しない。
使われ方：Stacks 19.12.2、TT §3 の各項単射性の比較。
-/
lemma descFromExtendedComplexComponent_eq {i : ι} {i' : ι'} (hi : e.f i = i') :
    descFromExtendedComplexComponent e φ i' =
      (L.extendXIso e hi).hom ≫ φ.f i ≫ (K.restrictionXIso e hi).hom := by
  classical
  have h : ∃ j, e.f j = i' := ⟨i, hi⟩
  have hh : h.choose = i := e.injective_f (by rw [h.choose_spec, hi])
  simp only [descFromExtendedComplexComponent, dite_eq_left h]
  subst hh
  rfl

/--
概要：外へ出る微分で零になる射を、零延長した始域からの鎖写像へ拡張する。
方針：像の内外で分け、内部の可換性と外部の零性を使う。
規約：全射や同型の存在を追加の公理として置かない。
使われ方：Stacks 19.12.2、TT §3 の小さい部分複体の実際の包含。
-/
def descFromExtendedComplex
    (hφ : ∀ (i : ι) (j' : ι'), (∀ j, e.f j ≠ j') → c'.Rel (e.f i) j' →
      φ.f i ≫ K.d (e.f i) j' = 0) : L.extend e ⟶ K where
  f := descFromExtendedComplexComponent e φ
  comm' i' j' hij := by
    classical
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi
      rw [descFromExtendedComplexComponent_eq e φ rfl]
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj
        rw [descFromExtendedComplexComponent_eq e φ rfl, L.extend_d_eq e rfl rfl]
        simp only [HomologicalComplex.restrictionXIso, eqToIso_refl, Iso.refl_hom,
          Category.comp_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
        have hc := φ.comm i j
        change φ.f i ≫ K.d (e.f i) (e.f j) = L.d i j ≫ φ.f j at hc
        simpa only [Category.assoc] using
          congrArg (fun u => (L.extendXIso e rfl).hom ≫ u) hc
      · have hz : (L.extend e).d (e.f i) j' = 0 :=
          (L.isZero_extend_X e j' (by simpa using hj)).eq_zero_of_tgt _
        rw [hz, zero_comp]
        dsimp [HomologicalComplex.restrictionXIso]
        rw [Category.comp_id, Category.assoc, hφ i j' (by simpa using hj) hij, comp_zero]
    · exact (L.isZero_extend_X e i' (by simpa using hi)).eq_of_src _ _

/--
概要：零延長した始域からの射は、元の各項の射が単射なら各項で単射となる。
方針：像の中では同型を挟んだ単射、像の外では零対象からの射を使う。
規約：全ての次数で検証する。
使われ方：Stacks 19.12.2、TT §3 の整数次数の部分複体の単射性。
-/
lemma descFromExtendedComplex_f_mono
    (hφ : ∀ (i : ι) (j' : ι'), (∀ j, e.f j ≠ j') → c'.Rel (e.f i) j' →
      φ.f i ≫ K.d (e.f i) j' = 0) [∀ i, Mono (φ.f i)] (i' : ι') :
    Mono ((descFromExtendedComplex e φ hφ).f i') := by
  classical
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    change Mono (descFromExtendedComplexComponent e φ i')
    rw [descFromExtendedComplexComponent_eq e φ hi]
    infer_instance
  · constructor
    intro Z f g hfg
    exact (L.isZero_extend_X e i' (by simpa using hi)).eq_of_tgt f g

end SerrePositivity.KST.DerivedGeometry
