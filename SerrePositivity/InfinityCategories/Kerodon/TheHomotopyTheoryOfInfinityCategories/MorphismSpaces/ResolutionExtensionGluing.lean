module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionAllFaces

/-!
概要：包含と可換な解像の同型を部分複体の和へ貼り合わせる。
方針：交わりと二つの部分の同型を、解像が保存する pushout の普遍性で和へ延長する。
規約：同型の条件には大きい標準単体の解像への包含との可換性を含める。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、明示的な境界と左 Kan 拡張の同定。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二つの pushout の張る図式の同型は貼り合わせた対象の同型を与える。
方針：片方の張る図式を同型で移し、同じ張る図式の余極限の一意性を使う。
規約：得られる同型には二つの包含との可換条件を添える。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、Proposition 4.6.7.23（Tag 01LW）、同型の貼り合わせ。 -/
lemma exists_pushoutIsoOfCompatibleIsos
    {Z X Y P Z' X' Y' P' : SSet.{u}}
    {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {i' : X' ⟶ P'} {j' : Y' ⟶ P'}
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (eZ : Z ≅ Z') (eX : X ≅ X') (eY : Y ≅ Y')
    (hf : f ≫ eX.hom = eZ.hom ≫ f') (hg : g ≫ eY.hom = eZ.hom ≫ g') :
    ∃ e : P ≅ P', i ≫ e.hom = eX.hom ≫ i' ∧ j ≫ e.hom = eY.hom ≫ j' := by
  have ht : IsPushout f g (eX.hom ≫ i') (eY.hom ≫ j') :=
    h'.of_iso' eZ eX eY (Iso.refl P') hf.symm hg.symm (by simp) (by simp)
  exact ⟨h.isoIsPushout X Y ht, h.inl_isoIsPushout_hom X Y ht,
    h.inr_isoIsPushout_hom X Y ht⟩

/-- 概要：標準単体の部分複体上の一般解像を明示的な部分複体と同定できる条件。
方針：二つの単体集合の同型に、大きい解像への包含との可換条件を添える。
規約：A は標準単体、B はその旗の解像の部分複体。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、同型の有限の貼り合わせの帰納条件。 -/
def HasCoherentResolutionExtension {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)
    (B : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex) : Prop :=
  ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj A.toSSet ≅ B.toSSet,
    e.hom ≫ B.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map A.ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌

/-- 概要：全ての面で一般解像と明示的な解像を同定できる。
方針：全ての面に対して選んだ同型と包含との可換性を使う。
規約：空の面も含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限帰納法の面の部分。 -/
lemma hasCoherentResolutionExtension_face {n : ℕ} (T : Finset (Fin (n + 1))) :
    HasCoherentResolutionExtension (stdSimplex.face.{u} T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceExtensionIsoAll T, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceExtensionIsoAll_hom_ι T⟩

/-- 概要：等しい部分複体へ移しても解像の同定条件は変わらない。
方針：二つの部分複体の等号を消去する。
規約：包含の等号は型の移送に含まれる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、交わりの面族への書き換え。 -/
lemma hasCoherentResolutionExtension_congr {n : ℕ}
    {A A' : (Δ[n] : SSet.{u}).Subcomplex}
    {B B' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex} (hA : A = A') (hB : B = B') :
    HasCoherentResolutionExtension A B ↔ HasCoherentResolutionExtension A' B' := by
  subst A'
  subst B'
  rfl

/-- 概要：包含と可換な二つの解像の同型は部分複体間の包含とも可換。
方針：大きい解像への単射な包含の後で比較し、同じ包含の像に戻す。
規約：同型の選択には追加の整合性を要求しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、pushout の張る図式の比較の二つの可換式。 -/
lemma coherentResolutionExtension_naturality {n : ℕ}
    {A A' : (Δ[n] : SSet.{u}).Subcomplex}
    {B B' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj A.toSSet ≅ B.toSSet)
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj A'.toSSet ≅ B'.toSSet)
    (he : e.hom ≫ B.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map A.ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌)
    (he' : e'.hom ≫ B'.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map A'.ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌)
    (hA : A ≤ A') (hB : B ≤ B') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (Subcomplex.homOfLE hA) ≫ e'.hom = e.hom ≫ Subcomplex.homOfLE hB := by
  apply (cancel_mono B'.ι).mp
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map A.ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ := by
      rw [Category.assoc, he', ← Category.assoc, ← CategoryTheory.Functor.map_comp,
        Subcomplex.homOfLE_ι]
    _ = _ := by rw [Category.assoc, Subcomplex.homOfLE_ι, he]

/-- 概要：二つの部分と交わりでの解像の同型は和の上へ延長できる。
方針：標準単体の側の pushout を解像で写し、明示的な側の pushout と同型で比較する。
規約：得られる和の同型も大きい解像への包含と可換。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の有限和と境界の同型の帰納段階。 -/
lemma hasCoherentResolutionExtension_sup {n : ℕ}
    (A₁ A₂ : (Δ[n] : SSet.{u}).Subcomplex)
    (B₁ B₂ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex)
    (hI : HasCoherentResolutionExtension (A₁ ⊓ A₂) (B₁ ⊓ B₂))
    (h₁ : HasCoherentResolutionExtension A₁ B₁)
    (h₂ : HasCoherentResolutionExtension A₂ B₂) :
    HasCoherentResolutionExtension (A₁ ⊔ A₂) (B₁ ⊔ B₂) := by
  obtain ⟨eI, heI⟩ := hI
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  let sqA : Subcomplex.BicartSq (A₁ ⊓ A₂) A₁ A₂ (A₁ ⊔ A₂) := ⟨rfl, rfl⟩
  let sqB : Subcomplex.BicartSq (B₁ ⊓ B₂) B₁ B₂ (B₁ ⊔ B₂) := ⟨rfl, rfl⟩
  have hP := sqA.isPushout.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution
  obtain ⟨e, hi, hj⟩ := exists_pushoutIsoOfCompatibleIsos hP sqB.isPushout eI e₁ e₂
    (coherentResolutionExtension_naturality eI e₁ heI he₁ sqA.le₁₂ sqB.le₁₂)
    (coherentResolutionExtension_naturality eI e₂ heI he₂ sqA.le₁₃ sqB.le₁₃)
  refine ⟨e, ?_⟩
  apply hP.hom_ext
  · rw [← Category.assoc, hi, Category.assoc, Subcomplex.homOfLE_ι, he₁,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι]
  · rw [← Category.assoc, hj, Category.assoc, Subcomplex.homOfLE_ι, he₂,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
