// Typewriter Animation JavaScript
function initTypewriter() {
  console.log('Typewriter script loaded');
  
  const typewriterElement = document.querySelector('.typewriter-text-enhanced');
  console.log('Typewriter element found:', typewriterElement);
  
  if (typewriterElement) {
    const text = typewriterElement.textContent.trim();
    console.log('Text to animate:', text);
    
    typewriterElement.textContent = '';
    typewriterElement.style.borderRight = '3px solid #3498db';
    typewriterElement.style.overflow = 'hidden';
    typewriterElement.style.whiteSpace = 'nowrap';
    
    let i = 0;
    let isDeleting = false;
    let cursorVisible = true;
    
    // Blinking cursor effect
    function blinkCursor() {
      if (cursorVisible) {
        typewriterElement.style.borderRight = '3px solid #3498db';
      } else {
        typewriterElement.style.borderRight = '3px solid transparent';
      }
      cursorVisible = !cursorVisible;
      setTimeout(blinkCursor, 500);
    }
    
    function typeWriter() {
      if (isDeleting) {
        // Deleting characters
        typewriterElement.textContent = text.substring(0, i);
        i--;
        
        if (i < 0) {
          isDeleting = false;
          setTimeout(typeWriter, 500); // Pause before typing again
        } else {
          setTimeout(typeWriter, 50); // Faster deletion
        }
      } else {
        // Typing characters
        typewriterElement.textContent = text.substring(0, i + 1);
        i++;
        
        if (i >= text.length) {
          isDeleting = true;
          setTimeout(typeWriter, 2000); // Pause before deleting
        } else {
          setTimeout(typeWriter, 100); // Typing speed
        }
      }
    }
    
    // Start the blinking cursor
    blinkCursor();
    
    // Start the animation after a delay
    setTimeout(typeWriter, 1000);
  } else {
    console.log('Typewriter element not found, retrying...');
    setTimeout(initTypewriter, 1000);
  }
}

// Try multiple ways to ensure the script runs
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', initTypewriter);
} else {
  initTypewriter();
}

// Also try after a delay as a fallback
setTimeout(initTypewriter, 2000);
