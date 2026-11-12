module
public import SerrePositivity.KST.SConstruction.CofiberPostcompLaws

/-! # 安定な入力上の単体的 S 自己関手
概要：零対象と cofiber を保つ射を持つ安定な quasicategory の圏上で S• を自己関手として構成する。
方針：既存の全 gapped S_n と構造射を保存条件付きで束ねる。
規約：Core・Stable の公開定義を変更しない。使われ方：多単体的な有限反復。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S 構成のための安定な単体集合の入力。
方針：底の単体集合と既存の quasicategory・安定性を束ねる。
規約：α-S の IsStable をそのまま用いる。使われ方：S の自己関手の定義域。 -/
structure StableModel where
  carrier : SSet.{u}
  [quasicategory : Quasicategory carrier]
  [stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable carrier]

attribute [instance] StableModel.quasicategory StableModel.stable

/-- 概要：安定な入力の射は零対象と cofiber を保つ単体的射。
方針：既存の保存条件を持つ射の部分型を使う。
規約：h 圏の関手へ置き換えない。使われ方：反復 S の関手法則。 -/
instance stableModelCategory : Category.{u} StableModel.{u} where
  Hom X Y := {f : X.carrier ⟶ Y.carrier // PreservesCofiberData f}
  id X := ⟨𝟙 X.carrier, preservesCofiberData_id X.carrier⟩
  comp f g := ⟨f.val ≫ g.val, PreservesCofiberData.comp f.property g.property⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- 概要：安定な入力の底の単体集合へ忘れる関手。
方針：保存条件の証明だけを忘れる。
規約：底の射は変えない。使われ方：core と対角実現への接続。 -/
def stableModelForget : StableModel.{u} ⥤ SSet.{u} where
  obj X := X.carrier
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：S_n を再び安定な入力として束ねる。
方針：S_n の quasicategory 性と安定性の証明を使う。
規約：n = 0 も含む。使われ方：S の反復。 -/
def sStableModel (n : ℕ) (X : StableModel.{u}) : StableModel.{u} :=
  { carrier := sConstruction n X.carrier
    quasicategory := inferInstance
    stable := inferInstance }

/-- 概要：S_n は安定な入力の圏の自己関手。
方針：cofiber 保存型の後合成とその保存条件・関手法則を束ねる。
規約：元の全 gapped S_n を使う。使われ方：多単体的反復の各段。 -/
def sEndofunctor (n : ℕ) : StableModel.{u} ⥤ StableModel.{u} where
  obj X := sStableModel n X
  map f := ⟨sPostcompCofiber n f.val f.property,
    preservesCofiberData_sPostcompCofiber n f.val f.property⟩
  map_id X := Subtype.ext (sPostcompCofiber_id n X.carrier)
  map_comp f g := Subtype.ext (sPostcompCofiber_comp n f.val g.val f.property g.property)

/-- 概要：各単体作用は S の自己関手間の自然変換。
方針：面・退化の保存条件と後合成との可換性を使う。
規約：自然性は厳密。使われ方：反復の別方向の作用の可換性。 -/
def sEndofunctorMap {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) :
    sEndofunctor.{u} n ⟶ sEndofunctor m where
  app X := ⟨sMap X.carrier θ, preservesCofiberData_sMap X.carrier θ⟩
  naturality {_X _Y} f := Subtype.ext (sPostcompCofiber_sMap f.val f.property θ)

/-- 概要：S• は安定な入力上の単体的自己関手。
方針：単体作用の恒等・合成法則を自然変換の各成分で確認する。
規約：全ての単体作用素を含む。使われ方：有限反復の多単体構造。 -/
def simplicialStableEndofunctor : SimplexCategoryᵒᵖ ⥤ (StableModel.{u} ⥤ StableModel.{u}) where
  obj n := sEndofunctor n.unop.len
  map θ := sEndofunctorMap θ.unop.toOrderHom
  map_id n := by
    apply NatTrans.ext
    funext X
    exact Subtype.ext (sMap_id n.unop.len X.carrier)
  map_comp θ φ := by
    apply NatTrans.ext
    funext X
    exact Subtype.ext (sMap_comp X.carrier φ.unop.toOrderHom θ.unop.toOrderHom)

end SerrePositivity.KST.SConstruction
