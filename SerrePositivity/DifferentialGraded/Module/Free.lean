module
public import SerrePositivity.DifferentialGraded.Module.Tensor
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 自由右 dg 加群の関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

/-- 左 tensor の因子の chain map を全次数自然な加群射へ持ち上げる。 -/
def tensorModuleMap {K L : Complex A} (g : K ⟶ L) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (tensorModule K M) ⟶
      ForgetEnrichment.of (Complex A) (tensorModule L M) :=
  moduleMorphismMk A D (M := tensorModule K M) (N := tensorModule L M)
    (fun x => g ⊗ₘ 𝟙 (M.obj x)) (by
      intro x y
      change (M.map x y ≫ tensorLeftHom K (M.obj x) (M.obj y)) ≫
          homPostcompose (K ⊗ M.obj x) (g ⊗ₘ 𝟙 (M.obj y)) =
        (M.map x y ≫ tensorLeftHom L (M.obj x) (M.obj y)) ≫
          homPrecompose (g ⊗ₘ 𝟙 (M.obj x)) (L ⊗ M.obj y)
      rw [Category.assoc, Category.assoc, tensorLeftHom_naturality])

/-- tensor 因子から持ち上げた加群射の成分。 -/
@[simp]
lemma tensorModuleMap_eval {K L : Complex A} (g : K ⟶ L) (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (tensorModuleMap g M) = g ⊗ₘ 𝟙 (M.obj (op x)) :=
  moduleMorphismMk_eval A D _ _ x

/-- 固定した右加群 M への左 tensor を複体の関手にする。 -/
@[implicit_reducible]
def tensorModuleFunctor (M : RightModule A D) : Complex A ⥤ ModuleCategory A D where
  obj K := ForgetEnrichment.of (Complex A) (tensorModule K M)
  map g := tensorModuleMap g M
  map_id K := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_id, tensorModuleMap_eval]
    simp
    rfl
  map_comp g h := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, tensorModuleMap_eval,
      tensorModuleMap_eval]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]

/-- x において複体 K で生成する自由右加群関手。 -/
abbrev freeAt (x : D) : Complex A ⥤ ModuleCategory A D :=
  tensorModuleFunctor (representable A x)

/-- 自由加群関手の対象成分は指定した tensor。 -/
lemma freeAt_obj (x y : D) (K : Complex A) :
    (moduleEvaluation A D y).obj ((freeAt x).obj K) = K ⊗ (y ⟶[Complex A] x) := rfl
end SerrePositivity.DifferentialGraded
