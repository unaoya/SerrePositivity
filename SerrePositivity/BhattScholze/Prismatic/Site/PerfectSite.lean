module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteSheaf
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.InducedTopology

/-!
# 完全 prismatic site

BS 著者版 Remark 4.6 の完全 prism の充満部分圏と誘導位相を定義する。
向き付きで濃度を制限した既存 site の部分圏を用い、比較定理はこの定義に含めない。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u})

/-- BS 著者版 Remark 4.6 の完全 prism の充満部分圏（環の向き）。
対象の有界性と濃度制限は PrismOver から引き継ぐ。 -/
abbrev PerfectPrismOver :=
  ObjectProperty.FullSubcategory (fun X : PrismOver P R κ => X.Q.deltaStructure.IsPerfect)

/-- 完全 prism の充満部分圏の包含。射には追加の条件を課さない。 -/
abbrev perfectPrismOverInclusion : PerfectPrismOver P R κ ⥤ PrismOver P R κ :=
  ObjectProperty.ι (fun X : PrismOver P R κ => X.Q.deltaStructure.IsPerfect)

/-- BS 著者版 Remark 4.6 の完全 prismatic site の台圏。
prism の圏の opposite を取る点は元の site と同じ。 -/
abbrev PerfectPrismaticSiteLarge := (PerfectPrismOver P R κ)ᵒᵖ

/-- 完全 prismatic site から元の site への包含。 -/
abbrev perfectPrismaticSiteInclusion : PerfectPrismaticSiteLarge P R κ ⥤ (PrismOver P R κ)ᵒᵖ :=
  (perfectPrismOverInclusion P R κ).op

/-- BS 著者版 Remark 4.6 の誘導位相。
許容 cutoff における元の平坦位相を充満部分圏に誘導する。 -/
def perfectPrismaticTopology (hκ : IsAdmissibleCutoff P R κ) :
    GrothendieckTopology (PerfectPrismaticSiteLarge P R κ) :=
  (perfectPrismaticSiteInclusion P R κ).inducedTopology (PrismOver.flatTopology hκ)

end SerrePositivity.BhattScholze.Prismatic
