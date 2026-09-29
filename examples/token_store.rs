//! `TokenStore`: keep values in a store and refer to them by a small token.
//!
//! Run with: `cargo run --example token_store`

use anythingy::{Token, TokenStore};

struct Texture {
    name: &'static str,
}

/// A renderer hands out tokens instead of the textures themselves.
struct Renderer {
    textures: TokenStore<Texture>,
}

impl Renderer {
    fn load(&mut self, name: &'static str) -> Token<Texture> {
        self.textures.insert(Texture { name })
    }

    fn draw(&self, texture: Token<Texture>) {
        match self.textures.get(texture) {
            Some(t) => println!("drawing with {}", t.name),
            None => println!("texture was unloaded, skipping"),
        }
    }
}

fn main() {
    let mut renderer = Renderer {
        textures: TokenStore::new(),
    };

    // Insert a value, get a token back. Tokens are small and `Copy`.
    let grass = renderer.load("grass");
    let rock = renderer.load("rock");
    renderer.draw(grass);
    renderer.draw(rock);

    // Remove a value; its token becomes stale.
    renderer.textures.remove(grass);
    renderer.draw(grass);

    // The space is reused for a new value, but the old token is still stale.
    let sand = renderer.load("sand");
    assert_ne!(sand, grass);
    renderer.draw(grass); // still stale
    renderer.draw(sand);

    // Iterate over everything that is stored.
    for texture in renderer.textures.values() {
        println!("stored: {}", texture.name);
    }
}
