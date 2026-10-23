module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorInverse

/-!
概要：同じ底上の left fibrations の同値による相対写像空間の後合成の同値性。
方針：底上の相対逆射の単位・余単位を豊穣後合成で写し、関手空間の逆データを得る。
規約：相対写像空間の始域の図式には充填性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening の復元比較による写像空間の標的の置き換え。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の射の相対写像空間内での同型は、任意の図式からの後合成の関手同型を与える。
方針：相対写像空間の豊穣後合成で同型を写し、通常の後合成の頂点と同定する。
規約：底上の対象 a、b、c の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、相対的な単位・余単位を後合成の逆データへ移す。 -/
noncomputable def relativeFunctorPostIso {B : SSet.{u}} (a b c : Over B) (f g : b ⟶ c)
    (η : VertexIso (relativeFunctorVertex c.hom b.hom f.left f.w)
      (relativeFunctorVertex c.hom b.hom g.left g.w)) :
    FunctorIso (HomotopyLimits.relativeFunctorPost b.hom c.hom f.left f.w a.hom)
      (HomotopyLimits.relativeFunctorPost b.hom c.hom g.left g.w a.hom) := by
  have h := VertexIso.map η (relativeFunctorPostHom a b c)
  simpa only [relativeFunctorPostHom_vertex] using h

/-- 概要：底上の left fibrations の前合成同値による後合成は任意の相対関手空間の同値。
方針：底上の逆射を相対関手へ後合成し、相対的な単位・余単位から二つの関手同型を作る。
規約：底 B は quasicategory。図式 a の定義域 A は任意。
使われ方：Kerodon Corollary 5.6.0.6、復元比較で相対写像空間の標的を置き換える。 -/
lemma relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    {A E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) (a : A ⟶ B) :
    IsQCatEquivalence (HomotopyLimits.relativeFunctorPost p q f hf a) := by
  obtain ⟨g, hg, ⟨hunit⟩, ⟨hcounit⟩⟩ :=
    exists_relativeFunctorInverse_of_precompositionEquivalence p q f hf ef
  let f' : Over.mk p ⟶ Over.mk q := Over.homMk f hf
  let g' : Over.mk q ⟶ Over.mk p := Over.homMk g hg
  have hu := relativeFunctorPostIso (Over.mk a) (Over.mk p) (Over.mk p)
    (f' ≫ g') (𝟙 _) hunit
  have hv := relativeFunctorPostIso (Over.mk a) (Over.mk q) (Over.mk q)
    (g' ≫ f') (𝟙 _) hcounit
  change FunctorIso (HomotopyLimits.relativeFunctorPost p p (f ≫ g) _ a)
    (HomotopyLimits.relativeFunctorPost p p (𝟙 E) _ a) at hu
  change FunctorIso (HomotopyLimits.relativeFunctorPost q q (g ≫ f) _ a)
    (HomotopyLimits.relativeFunctorPost q q (𝟙 F) _ a) at hv
  rw [← relativeFunctorPost_comp p q p f hf g hg a, relativeFunctorPost_id] at hu
  rw [← relativeFunctorPost_comp q p q g hg f hf a, relativeFunctorPost_id] at hv
  exact ⟨HomotopyLimits.relativeFunctorPost q p g hg a, ⟨hu⟩, ⟨hv⟩⟩

/-- 概要：底上の同値による相対後合成は全ての quasicategory への前合成同値。
方針：相対写像空間の後合成の quasicategory の同値性を前合成の判定へ移す。
規約：実際の後合成の射の性質として述べる。
使われ方：Kerodon Corollary 5.6.0.6、相対写像空間の同値の合成。 -/
lemma relativeFunctorPost_isPrecompositionEquivalence_of_precompositionEquivalence
    {A E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) (a : A ⟶ B) :
    IsPrecompositionEquivalence (HomotopyLimits.relativeFunctorPost p q f hf a) :=
  (relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence p q f hf ef a).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
