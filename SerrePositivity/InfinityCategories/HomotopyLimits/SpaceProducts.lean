module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits

/-!
概要：Kan 複体の実際の積を空間の ∞ 圏 𝒮 の極限錐として公開する。
方針：台の単体集合の積を Kan 複体に束縛し、全 Hom の極限性を検証して γ3 の移送を使う。
規約：F1 の kanDiagramCoherentNerve を底の図式とし、有限性を仮定しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6、γ3c と F2 の 𝒮 の積。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {J : Type u}

/-- 概要：小さい Kan 複体の族の積を Kan 複体として束縛する。
方針：台の単体集合の strict 極限と離散極限の Kan 性を使う。
規約：J は任意で、空積も含む。
使われ方：Kerodon 7.5.4.6 の 𝒮 の実際の積の対象。 -/
noncomputable def kanProductObject (F : Discrete J ⥤ KanObject.{u}) : KanObject.{u} := by
  have : ∀ i, KanComplex ((F ⋙ kanObjectForget).obj i) := fun i ↦
    inferInstanceAs (KanComplex (F.obj i).obj)
  exact ⟨limit (F ⋙ kanObjectForget), inferInstance⟩

/-- 概要：Kan 複体の族の積の射影からなる通常の錐。
方針：台の単体集合の積の射影を、Kan 複体の圏の射として使う。
規約：頂点は kanProductObject F そのもの。
使われ方：HTT 4.2.4.1 の strict な積の錐の入力。 -/
noncomputable def kanProductCone (F : Discrete J ⥤ KanObject.{u}) : Cone F where
  pt := kanProductObject F
  π := Discrete.natTrans (fun i ↦ limit.π (F ⋙ kanObjectForget) i)

/-- 概要：Kan 複体の積の錐は台の単体集合の極限錐。
方針：台の射影を標準の極限錐の射影に同定する。
規約：追加の Hom 条件を仮定しない。
使われ方：Kerodon 7.5.4.6 の豊穣 Hom の極限条件の検証。 -/
noncomputable def kanProductCone_forget_isLimit (F : Discrete J ⥤ KanObject.{u}) :
    IsLimit (kanObjectForget.mapCone (kanProductCone F)) := by
  exact limit.isLimit (F ⋙ kanObjectForget)

/-- 概要：束縛した積の対象と射影は通常の Kan 複体の圏の積を与える。
方針：台の単体集合の極限の普遍性を Kan 複体の錐へ戻す。
規約：全ての小さい族を扱う。
使われ方：Kerodon 7.5.4.6 の ∞ 積へ移す実際の strict な積。 -/
noncomputable def kanProductCone_isLimit (F : Discrete J ⥤ KanObject.{u}) :
    IsLimit (kanProductCone F) :=
  kanObjectCone_isLimit_of_forget _ (kanProductCone_forget_isLimit F)

/-- 概要：空間の ∞ 圏の既存の図式上の積の錐。
方針：通常の Kan 複体の積の錐を coherent nerve へ写し、F1 の図式の表示へ同定する。
規約：底は kanDiagramCoherentNerve F、頂点の対象は kanProductObject F。
使われ方：HTT 4.2.4.1 の双対、γ3c・F2 が使う 𝒮 の具体的な積の錐。 -/
noncomputable def spaceProductCone (F : Discrete J ⥤ KanObject.{u}) :
    JoinCone (kanDiagramCoherentNerve F) :=
  (strictCoherentCone (kanProductCone F)).cast (strictCoherentDiagram_eq_kanDiagram F)

/-- 概要：空間の積の錐の頂点は実際の Kan 複体の積の標準頂点。
方針：図式の移送は頂点を変えず、strict な錐の頂点の計算を使う。
規約：同値類ではなく頂点の等号。
使われ方：Kerodon 7.5.4.6 の ∞ 積の対象の明示。 -/
lemma spaceProductCone_vertex (F : Discrete J ⥤ KanObject.{u}) :
    (spaceProductCone F).vertex = spaceInfinityVertex (kanProductObject F) := by
  rw [spaceProductCone, JoinCone.vertex_cast, strictCoherentCone_vertex,
    spaceInfinityVertex_eq_coherent]
  rfl

/-- 概要：Kan 複体の実際の積の錐は空間の ∞ 圏 𝒮 の極限錐である。
方針：台の積の普遍性から全 Hom の極限性を検証し、離散 homotopy 極限の移送を適用する。
規約：J に有限性は不要。Hom の比較の同値性を追加の仮定にしない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6、γ3c の有限積を含む 𝒮 の積。 -/
lemma spaceProductCone_isLimitCone (F : Discrete J ⥤ KanObject.{u}) :
    IsLimitCone (spaceProductCone F) := by
  apply IsLimitCone.cast
  exact strictCoherentCone_isLimit_of_discrete_homLimit (kanProductCone F)
    (kanObjectHomCone_isLimit_of_forget _ (kanProductCone_forget_isLimit F))

end SerrePositivity.InfinityCategories.HomotopyLimits
