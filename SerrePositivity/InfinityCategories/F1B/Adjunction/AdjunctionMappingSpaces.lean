module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantAdjunct
public import SerrePositivity.InfinityCategories.F1B.Fibrations.RightHomotopySquare
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：随伴から区間模型の写像空間のホモトピー同値を構成する。
方針：普遍的な族の adjunct を族で表し、自然性とホモトピーまでの単射性で両逆を示す。
規約：ここでは区間模型を使う。pinched 模型への比較と逆の特徴づけは別に要する。
使われ方：Kerodon Prop 6.2.1.17、HTT §5.2 の写像空間による随伴の特徴づけの順方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.QCatAdjunction

/-- 概要：随伴が与える区間模型の写像空間の間の射。
方針：始域の恒等族の adjunct を、全射性によって実際の族で表す。
規約：代表の選択を使う。両逆はホモトピーで証明する。
使われ方：Kerodon Prop 6.2.1.17 の順対応。 -/
noncomputable def intervalMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) :=
  Classical.choose (intervalFamilyHom_surjective _ _ x (G.app (Opposite.op ⦋0⦌) y)
    (a.constantHomEquiv _ x y (intervalFamilyHom (𝟙 _))))

/-- 概要：比較射が表す h Fun の射は指定された adjunct。
方針：全射性による代表の選択の条件を読む。
規約：実際に選んだ同じ射を使う。
使われ方：比較射の合成が恒等族を表すことの計算。 -/
lemma intervalMap_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalFamilyHom (a.intervalMap x y) = a.constantHomEquiv _ x y (intervalFamilyHom (𝟙 _)) :=
  Classical.choose_spec (intervalFamilyHom_surjective _ _ x (G.app (Opposite.op ⦋0⦌) y)
    (a.constantHomEquiv _ x y (intervalFamilyHom (𝟙 _))))

/-- 概要：区間模型の比較射の逆向きの候補。
方針：終域の恒等族の逆 adjunct を実際の族で表す。
規約：代表の選択を使い、厳密な逆射とは主張しない。
使われ方：Kerodon Prop 6.2.1.17 のホモトピー逆。 -/
noncomputable def intervalInverse {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) ⟶
      intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y :=
  Classical.choose (intervalFamilyHom_surjective _ _ (F.app (Opposite.op ⦋0⦌) x) y
    ((a.constantHomEquiv _ x y).symm (intervalFamilyHom (𝟙 _))))

/-- 概要：逆向きの候補が表す h Fun の射は指定された逆 adjunct。
方針：代表の選択の条件を使う。
規約：intervalInverse で選んだ同じ射。
使われ方：両合成のホモトピーの計算。 -/
lemma intervalInverse_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalFamilyHom (a.intervalInverse x y) =
      (a.constantHomEquiv _ x y).symm (intervalFamilyHom (𝟙 _)) :=
  Classical.choose_spec (intervalFamilyHom_surjective _ _ (F.app (Opposite.op ⦋0⦌) x) y
    ((a.constantHomEquiv _ x y).symm (intervalFamilyHom (𝟙 _))))

/-- 概要：比較射は任意のパラメータ族の adjunct を表す。
方針：普遍族での定義とパラメータ自然性を使う。
規約：A は quasicategory。族 f は任意の射。
使われ方：Kerodon Prop 6.2.1.17 の比較のパラメータ付きの仕様。 -/
lemma intervalMap_family {A X Y : SSet.{u}} [Quasicategory A]
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    intervalFamilyHom (f ≫ a.intervalMap x y) =
      a.constantHomEquiv A x y (intervalFamilyHom f) := by
  rw [intervalFamilyHom_precomp, intervalMap_hom, ← constantHomEquiv_precomp,
    ← intervalFamilyHom_precomp, Category.comp_id]

/-- 概要：逆比較射は任意のパラメータ族の逆 adjunct を表す。
方針：逆の普遍族の定義と逆対応の自然性を使う。
規約：A は quasicategory。族 f は任意。
使われ方：ホモトピー逆のパラメータ付きの仕様。 -/
lemma intervalInverse_family {A X Y : SSet.{u}} [Quasicategory A]
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)) :
    intervalFamilyHom (f ≫ a.intervalInverse x y) =
      (a.constantHomEquiv A x y).symm (intervalFamilyHom f) := by
  rw [intervalFamilyHom_precomp, intervalInverse_hom, ← constantHomEquiv_symm_precomp,
    ← intervalFamilyHom_precomp, Category.comp_id]

/-- 概要：指定された adjunct を表す比較射はホモトピーまで一意。
方針：同じ h Fun の射を表す二つの族のホモトピーを使う。
規約：代表の選択から生じる任意性を実際の単体的ホモトピーで比較する。
使われ方：区間模型の比較射の選択独立性。 -/
lemma intervalMap_unique_homotopy {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y))
    (hf : intervalFamilyHom f = a.constantHomEquiv _ x y (intervalFamilyHom (𝟙 _))) :
    Nonempty (SSet.Homotopy f (a.intervalMap x y)) :=
  intervalFamilyHom_eq_imp_homotopy (hf.trans (a.intervalMap_hom x y).symm)

/-- 概要：比較射の後に逆候補を続けると恒等射にホモトピック。
方針：自然性と adjunct の逆則で恒等族と同じ h Fun の射になることを示す。
規約：ホモトピーは区間模型の実際の単体的ホモトピー。
使われ方：Kerodon Prop 6.2.1.17 の第一の逆則。 -/
lemma intervalMap_inverse_homotopy {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Nonempty (SSet.Homotopy (a.intervalMap x y ≫ a.intervalInverse x y) (𝟙 _)) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalFamilyHom_precomp, intervalInverse_hom, ← constantHomEquiv_symm_precomp,
    ← intervalFamilyHom_precomp, Category.comp_id, intervalMap_hom, Equiv.symm_apply_apply]

/-- 概要：逆候補の後に比較射を続けても恒等射にホモトピック。
方針：自然性と adjunct のもう一方の逆則を使う。
規約：同じ二つの選ばれた比較射を使う。
使われ方：Kerodon Prop 6.2.1.17 の第二の逆則。 -/
lemma intervalInverse_map_homotopy {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Nonempty (SSet.Homotopy (a.intervalInverse x y ≫ a.intervalMap x y) (𝟙 _)) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalFamilyHom_precomp, intervalMap_hom, ← constantHomEquiv_precomp,
    ← intervalFamilyHom_precomp, Category.comp_id, intervalInverse_hom, Equiv.apply_symm_apply]

/-- 概要：随伴の比較射は区間模型の写像空間のホモトピー同値。
方針：選んだ逆射と両合成の実際のホモトピーを束ねる。
規約：pinched 模型への比較・対象の射に関する自然性・特徴づけの逆向きは別項目。
使われ方：Kerodon Prop 6.2.1.17 の順方向の区間模型版。 -/
lemma intervalMap_isSimplicialHomotopyEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (a.intervalMap x y) :=
  ⟨a.intervalInverse x y, a.intervalMap_inverse_homotopy x y, a.intervalInverse_map_homotopy x y⟩

end SerrePositivity.InfinityCategories.QCatAdjunction
