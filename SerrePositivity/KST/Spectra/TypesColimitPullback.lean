module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：単射な余極限の比較射と、成分ごとの pullback から余極限の pullback を構成する。
方針：標的の余極限の元を成分で代表し、その成分の pullback で持ち上げる。
規約：余極限全般の pullback 保存を仮定せず、実際の余錐と単射を使う。
使われ方：Goerss–Jardine VIII §1。骨格間の latching 正方形の共通部分。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.KST.Spectra.TypesColimitPullback
noncomputable section

/-- 余極限の各成分の pullback は、単射な比較射の下で全体の pullback になる。 -/
lemma of_components {J : Type v} [SmallCategory J] {F G : J ⥤ Type u}
    (c : Cocone F) (d : Cocone G) (hd : IsColimit d) (α : F ⟶ G)
    {X Y : Type u} (t : c.pt ⟶ d.pt) (l : c.pt ⟶ X) (r : d.pt ⟶ Y) (b : X ⟶ Y)
    [Mono l] (hw : t ≫ r = l ≫ b)
    (ht : ∀ j, c.ι.app j ≫ t = α.app j ≫ d.ι.app j)
    (hsq : ∀ j, IsPullback (α.app j) (c.ι.app j ≫ l) (d.ι.app j ≫ r) b) :
    IsPullback t l r b := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨hw, ?_, ?_⟩
  · intro x y h
    exact (mono_iff_injective l).1 inferInstance h.2
  · intro y x h
    obtain ⟨j, z, rfl⟩ := Types.jointly_surjective_of_isColimit hd y
    obtain ⟨a, ha, hx⟩ := Types.exists_of_isPullback (hsq j) z x h
    refine ⟨c.ι.app j a, ?_, hx⟩
    have he := ConcreteCategory.congr_hom (ht j) a
    exact he.trans (congrArg (d.ι.app j) ha)

end
end SerrePositivity.KST.Spectra.TypesColimitPullback
